import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesClassificationNorm
open CompleteModulesLipSDP CompleteModulesLipSDPProduct
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem actual_distinct_class_basis_difference_has_norm_sqrt_two
    (first second : O) (hdistinct : first≠second) :
    ‖WithLp.toLp 2 ((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ))‖=Real.sqrt 2 := by
  have hs : ‖WithLp.toLp 2 ((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ))‖^2=2 := by
    rw [squared_norm_of_coordinates]
    have he : (fun coordinate => (((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ)) coordinate)^2)=
        fun coordinate => (if coordinate=first then (1:ℝ) else 0)+(if coordinate=second then (1:ℝ) else 0) := by
      ext coordinate
      by_cases hf : coordinate=first <;> by_cases hs : coordinate=second
      · exact False.elim (hdistinct (hf.symm.trans hs))
      · simp [Pi.single_apply,hf,hs,hdistinct,hdistinct.symm]
      · simp [Pi.single_apply,hf,hs,hdistinct,hdistinct.symm]
      · simp [Pi.single_apply,hf,hs,hdistinct,hdistinct.symm]
    rw [he,Finset.sum_add_distrib]
    simp
    norm_num
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [norm_nonneg (WithLp.toLp 2 ((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ))),Real.sqrt_nonneg (2:ℝ)]

theorem actual_class_row_difference_is_adjoint_basis_difference
    (weight : Matrix O I ℝ) (first second : O) :
    weightᵀ *ᵥ ((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ))=
      fun coordinate => weight first coordinate-weight second coordinate := by
  ext coordinate
  simp [Matrix.mulVec_sub,Matrix.mulVec_single,Matrix.transpose_apply]

theorem actual_class_row_difference_norm_is_bounded_by_sqrt_two_spectral_norm
    (weight : Matrix O I ℝ) (first second : O) (hdistinct : first≠second) :
    ‖WithLp.toLp 2 (fun coordinate => weight first coordinate-weight second coordinate)‖ ≤
      Real.sqrt 2*‖weight‖ := by
  have h := actual_spectral_matrix_gain weightᵀ ((Pi.single first (1:ℝ) : O → ℝ)-(Pi.single second (1:ℝ) : O → ℝ))
  rw [actual_class_row_difference_is_adjoint_basis_difference,
    actual_distinct_class_basis_difference_has_norm_sqrt_two first second hdistinct] at h
  have hn : ‖weightᵀ‖=‖weight‖ := Matrix.l2_opNorm_conjTranspose weight
  rw [hn,mul_comm] at h
  exact h

theorem actual_one_vs_rest_global_radius_is_no_larger_than_pairwise_radius
    (margin rowGain globalGain : ℝ) (hmargin : 0 ≤ margin)
    (hrow : 0 < rowGain) (hglobal : 0 < globalGain)
    (hbound : rowGain ≤ Real.sqrt 2*globalGain) :
    margin/(Real.sqrt 2*globalGain) ≤ margin/rowGain := by
  exact div_le_div_of_nonneg_left hmargin hrow hbound

def actualQuarterScaleNormalizer (center input : I → ℝ) : I → ℝ :=
  fun coordinate => (input coordinate-center coordinate)/(1/4:ℝ)

theorem actual_quarter_scale_normalizer_increment (center first second : I → ℝ) :
    actualQuarterScaleNormalizer center first-actualQuarterScaleNormalizer center second=
      (4:ℝ) • (first-second) := by
  ext coordinate
  simp [actualQuarterScaleNormalizer]
  ring

theorem actual_quarter_scale_normalizer_distance (center first second : I → ℝ) :
    ‖WithLp.toLp 2 (actualQuarterScaleNormalizer center first-actualQuarterScaleNormalizer center second)‖=
      4*‖WithLp.toLp 2 (first-second)‖ := by
  rw [actual_quarter_scale_normalizer_increment]
  have he : WithLp.toLp 2 ((4:ℝ) • (first-second))=(4:ℝ) • WithLp.toLp 2 (first-second) := rfl
  rw [he,norm_smul]
  norm_num

theorem actual_normalized_radius_corresponds_to_pixel_radius
    (center first second : I → ℝ) (radius : ℝ) :
    ‖WithLp.toLp 2 (actualQuarterScaleNormalizer center first-actualQuarterScaleNormalizer center second)‖ < radius ↔
      ‖WithLp.toLp 2 (first-second)‖ < radius/4 := by
  rw [actual_quarter_scale_normalizer_distance,lt_div_iff₀ (show (0:ℝ) < 4 by norm_num)]
  rw [mul_comm]

end SafeLearning.CompleteModulesClassificationNorm
