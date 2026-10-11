import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesGeneralNormalization
open CompleteModulesLipSDPProduct
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def actualPerChannelNormalizationGain (scale : I → ℝ) : ℝ :=
  (Finset.univ.image (fun coordinate => 1/scale coordinate)).max'
    (Finset.univ_nonempty.image _)

def actualPerChannelNormalizer (center scale : I → ℝ) (input : EuclideanSpace ℝ I) :
    EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun coordinate => (WithLp.ofLp input coordinate-center coordinate)/scale coordinate)

theorem actual_per_channel_normalization_gain_is_positive
    (scale : I → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    0 < actualPerChannelNormalizationGain scale := by
  unfold actualPerChannelNormalizationGain
  obtain ⟨coordinate⟩ := ‹Nonempty I›
  exact (one_div_pos.mpr (hscale coordinate)).trans_le
    (Finset.le_max' (Finset.univ.image (fun coordinate : I => 1/scale coordinate)) (1/scale coordinate)
      (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩))

theorem actual_per_channel_diagonal_spectral_norm_equals_maximum_inverse_scale
    (scale : I → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    ‖Matrix.diagonal (fun coordinate => 1/scale coordinate)‖=
      actualPerChannelNormalizationGain scale := by
  rw [Matrix.l2_opNorm_diagonal]
  unfold actualPerChannelNormalizationGain
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (actual_per_channel_normalization_gain_is_positive scale hscale).le).mpr
    intro coordinate
    rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (hscale coordinate))]
    exact Finset.le_max' (Finset.univ.image (fun coordinate : I => 1/scale coordinate)) (1/scale coordinate)
      (Finset.mem_image.mpr ⟨coordinate,Finset.mem_univ _,rfl⟩)
  · apply Finset.max'_le
    intro value hvalue
    obtain ⟨coordinate,hcoordinate,he⟩ := Finset.mem_image.mp hvalue
    rw [← he]
    simpa only [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (hscale coordinate))] using
      (norm_le_pi_norm (fun coordinate => 1/scale coordinate) coordinate)

theorem actual_per_channel_normalizer_increment_is_diagonal_action
    (center scale : I → ℝ) (first second : EuclideanSpace ℝ I) :
    actualPerChannelNormalizer center scale first-actualPerChannelNormalizer center scale second=
      WithLp.toLp 2 (Matrix.diagonal (fun coordinate => 1/scale coordinate) *ᵥ
        (WithLp.ofLp first-WithLp.ofLp second)) := by
  rw [actualPerChannelNormalizer,actualPerChannelNormalizer,← WithLp.toLp_sub]
  congr 1
  ext coordinate
  simp only [Pi.sub_apply,Matrix.mulVec_diagonal,Pi.mul_apply]
  ring

theorem actual_per_channel_normalizer_is_lipschitz_with_maximum_inverse_scale
    (center scale : I → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (first second : EuclideanSpace ℝ I) :
    dist (actualPerChannelNormalizer center scale first) (actualPerChannelNormalizer center scale second) ≤
      actualPerChannelNormalizationGain scale*dist first second := by
  rw [dist_eq_norm,actual_per_channel_normalizer_increment_is_diagonal_action]
  have h := actual_spectral_matrix_gain (Matrix.diagonal (fun coordinate => 1/scale coordinate))
    (WithLp.ofLp first-WithLp.ofLp second)
  rw [actual_per_channel_diagonal_spectral_norm_equals_maximum_inverse_scale scale hscale] at h
  simpa only [WithLp.toLp_sub,WithLp.toLp_ofLp,dist_eq_norm] using h

theorem actual_preprocessing_multiplies_the_classifier_lipschitz_bound
    {O : Type*} [Fintype O] (center scale : I → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (classifier : EuclideanSpace ℝ I → EuclideanSpace ℝ O) (gain : ℝ) (hgain : 0 ≤ gain)
    (hclassifier : ∀ first second,dist (classifier first) (classifier second) ≤ gain*dist first second)
    (first second : EuclideanSpace ℝ I) :
    dist (classifier (actualPerChannelNormalizer center scale first))
      (classifier (actualPerChannelNormalizer center scale second)) ≤
        (gain*actualPerChannelNormalizationGain scale)*dist first second := by
  have h := mul_le_mul_of_nonneg_left
    (actual_per_channel_normalizer_is_lipschitz_with_maximum_inverse_scale center scale hscale first second) hgain
  exact (hclassifier _ _).trans (by simpa only [mul_assoc] using h)

end SafeLearning.CompleteModulesGeneralNormalization
