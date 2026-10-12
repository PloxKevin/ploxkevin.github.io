import SafeLearning.CompleteFoundationsNormMaterial
import SafeLearning.CompleteModulesGeneralMargin
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped BigOperators Matrix RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsLiteralCauchySchwarzUses28
open CompleteFoundationsNormDuality

section Euclidean
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_bounded_disturbance_has_the_literal_dual_row_bound
    (a d : I → ℝ) (dbar : ℝ) (hd : l2Norm d≤dbar) :
    |a ⬝ᵥ d|≤l2Norm a*dbar := by
  have h := abs_real_inner_le_norm (euclidean a) (euclidean d)
  rw [actual_euclidean_pairing_is_dot] at h
  exact h.trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))

theorem actual_ball_actuator_support_has_the_literal_attained_maximum
    (b : I → ℝ) (umax : ℝ) (hu : 0≤umax) :
    IsGreatest ((fun u : I → ℝ => b ⬝ᵥ u) '' {u | l2Norm u≤umax})
      (umax*l2Norm b) := by
  have hg := CompleteFoundationsNormMaterial.actual_shifted_ball_support_is_greatest
    (euclidean b) (0 : EuclideanSpace ℝ I) umax hu
  rcases hg.1 with ⟨u,huu,heu⟩
  refine ⟨⟨WithLp.ofLp u,?_,?_⟩,?_⟩
  · simpa only [l2Norm,euclidean,WithLp.toLp_ofLp,norm_sub_zero] using huu
  · have hpair : b ⬝ᵥ WithLp.ofLp u=⟪euclidean b,u⟫ := by
      simpa only [euclidean,WithLp.toLp_ofLp] using
        (actual_euclidean_pairing_is_dot b (WithLp.ofLp u)).symm
    rw [hpair]
    simpa only [inner_zero_right,zero_add,l2Norm] using heu
  · rintro value ⟨other,hother,rfl⟩
    have ho : euclidean other ∈ {u : EuclideanSpace ℝ I | ‖u-0‖≤umax} := by
      simpa only [mem_setOf_eq,norm_sub_zero,l2Norm] using hother
    have hh := hg.2 ⟨euclidean other,ho,rfl⟩
    simpa only [actual_euclidean_pairing_is_dot,inner_zero_right,zero_add] using hh

end Euclidean

section Classification
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def actualClassContrast (winner other : O) : O → ℝ := Pi.single winner 1-Pi.single other 1

theorem actual_distinct_class_contrast_has_the_printed_norm
    (winner other : O) (hdistinct : winner≠other) :
    l2Norm (actualClassContrast winner other)=Real.sqrt 2 :=
  CompleteModulesClassificationNorm.actual_distinct_class_basis_difference_has_norm_sqrt_two
    winner other hdistinct

theorem actual_class_contrast_dot_product_is_the_literal_logit_difference
    (winner other : O) (logits : O → ℝ) :
    actualClassContrast winner other ⬝ᵥ logits=logits winner-logits other := by
  simp [actualClassContrast,sub_dotProduct]

theorem actual_euclidean_lipschitz_logits_have_the_printed_margin_increment_bound
    (f : EuclideanSpace ℝ I → EuclideanSpace ℝ O) (L : ℝ≥0)
    (hf : LipschitzWith L f) (winner other : O) (hdistinct : winner≠other)
    (x δ : EuclideanSpace ℝ I) :
    |((f (x+δ)) winner-(f (x+δ)) other)-((f x) winner-(f x) other)|≤
      Real.sqrt 2*(L:ℝ)*‖δ‖ := by
  let logits : EuclideanSpace ℝ I → O → ℝ := fun z => WithLp.ofLp (f z)
  have hgain : ∀ first second,
      ‖WithLp.toLp 2 (logits first-logits second)‖≤(L:ℝ)*dist first second := by
    intro first second
    simpa only [dist_eq_norm] using hf.dist_le_mul first second
  have h := CompleteModulesGeneralMargin.actual_arbitrary_logit_global_gain_certifies_gap_gain
    logits (L:ℝ) hgain winner other hdistinct (x+δ) x
  simpa only [logits,dist_eq_norm,add_sub_cancel_left] using h

end Classification

section InverseMetric
variable {I : Type*} [Fintype I] [DecidableEq I]

def actualInverseInner (H : Matrix I I ℝ) (u v : I → ℝ) : ℝ := u ⬝ᵥ (H⁻¹ *ᵥ v)

theorem actual_positive_metric_inverse_form_has_every_inner_product_axiom
    (H : Matrix I I ℝ) (hH : H.PosDef) (u v w : I → ℝ) (a : ℝ) :
    H⁻¹.PosDef ∧
    actualInverseInner H u v=actualInverseInner H v u ∧
    actualInverseInner H (u+v) w=actualInverseInner H u w+actualInverseInner H v w ∧
    actualInverseInner H u (v+w)=actualInverseInner H u v+actualInverseInner H u w ∧
    actualInverseInner H (a • u) v=a*actualInverseInner H u v ∧
    actualInverseInner H u (a • v)=a*actualInverseInner H u v ∧
    (u≠0 → 0<actualInverseInner H u u) := by
  have hInv := hH.inv
  have ht : (H⁻¹).transpose=H⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hInv.isHermitian.eq
  refine ⟨hInv,?_,?_,?_,?_,?_,?_⟩
  · dsimp [actualInverseInner]
    rw [Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,ht,dotProduct_comm]
  · simp [actualInverseInner,add_dotProduct]
  · simp [actualInverseInner,Matrix.mulVec_add,dotProduct_add]
  · simp [actualInverseInner,smul_dotProduct]
  · simp [actualInverseInner,Matrix.mulVec_smul,dotProduct_smul]
  · intro hu
    simpa only [actualInverseInner,star_trivial] using hInv.dotProduct_mulVec_pos hu

theorem actual_cpo_source_q_s_product_bounds_the_true_cross_form_square
    (H : Matrix I I ℝ) (hH : H.PosDef) (g b : I → ℝ) :
    (g ⬝ᵥ (H⁻¹ *ᵥ g))*(b ⬝ᵥ (H⁻¹ *ᵥ b))≥(g ⬝ᵥ (H⁻¹ *ᵥ b))^2 := by
  have h := hH.inv.star_dotProduct_mulVec_mul_le g b
  simpa only [star_trivial,pow_two] using h

end InverseMetric
end SafeLearning.CompleteFoundationsLiteralCauchySchwarzUses28
