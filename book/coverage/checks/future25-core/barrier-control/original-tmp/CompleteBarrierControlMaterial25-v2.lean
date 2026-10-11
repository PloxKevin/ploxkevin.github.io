import SafeLearning.CompleteBarrierControlAffine

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteBarrierControlMaterial25

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem actual_pointwise_control_affine_chain_rule
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (x : ℝ → E) (u : ℝ → U) (t : ℝ) (L : E →L[ℝ] ℝ)
    (hh : HasFDerivAt h L (x t))
    (hx : HasDerivAt x (f (x t) + g (x t) (u t)) t) :
    HasDerivAt (h ∘ x) (L (f (x t)) + L (g (x t) (u t))) t := by
  simpa only [map_add] using hh.comp_hasDerivAt t hx

theorem actual_c1_control_affine_chain_rule
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (x : ℝ → E) (u : ℝ → U) (t : ℝ)
    (hh : ContDiffAt ℝ 1 h (x t))
    (hx : HasDerivAt x (f (x t) + g (x t) (u t)) t) :
    HasDerivAt (h ∘ x)
      (fderiv ℝ h (x t) (f (x t)) + fderiv ℝ h (x t) (g (x t) (u t))) t := by
  exact actual_pointwise_control_affine_chain_rule h f g x u t _
    (hh.differentiableAt (by decide)).hasFDerivAt hx

theorem actual_input_affine_combination
    (L : E →L[ℝ] ℝ) (f : E) (g : U →L[ℝ] E)
    (u v : U) (a b : ℝ) (hab : a + b = 1) :
    L (f + g (a • u + b • v)) =
      a * L (f + g u) + b * L (f + g v) := by
  simp only [map_add,map_smul,smul_eq_mul]
  linear_combination -(L f) * hab

theorem actual_barrier_input_halfspace_convex
    (L : E →L[ℝ] ℝ) (f : E) (g : U →L[ℝ] E) (threshold : ℝ) :
    Convex ℝ {u : U | threshold ≤ L (f + g u)} := by
  intro u hu v hv a b ha hb hab
  change threshold ≤ L (f + g (a • u + b • v))
  rw [actual_input_affine_combination L f g u v a b hab]
  have hau := mul_le_mul_of_nonneg_left hu ha
  have hbv := mul_le_mul_of_nonneg_left hv hb
  have hsum : threshold = a * threshold + b * threshold := by
    nlinarith [congrArg (fun z : ℝ => z * threshold) hab]
  rw [hsum]
  exact add_le_add hau hbv

theorem actual_barrier_input_constraint_is_linear
    (L : E →L[ℝ] ℝ) (f : E) (g : U →L[ℝ] E) (u : U) (threshold : ℝ) :
    threshold ≤ L (f + g u) ↔ threshold - L f ≤ (L.comp g) u := by
  simp only [map_add,ContinuousLinearMap.comp_apply]
  constructor <;> intro H <;> linarith

theorem actual_nominal_squared_cost_nonnegative
    {n : ℕ} (u nominal : Fin n → ℝ) :
    0 ≤ ∑ i, (u i - nominal i) ^ 2 := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem actual_nominal_squared_cost_quadratic_form
    {n : ℕ} (u nominal : Fin n → ℝ) :
    (∑ i, (u i - nominal i) ^ 2) =
      (∑ i, u i ^ 2) - 2 * (∑ i, u i * nominal i) + ∑ i, nominal i ^ 2 := by
  calc
    (∑ i, (u i - nominal i) ^ 2) =
        ∑ i, (u i ^ 2 - 2 * (u i * nominal i) + nominal i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]

end SafeLearning.CompleteBarrierControlMaterial25
