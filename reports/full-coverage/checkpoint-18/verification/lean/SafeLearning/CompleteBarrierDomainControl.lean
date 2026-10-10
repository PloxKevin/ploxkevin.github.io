import SafeLearning.CompleteBarrierVectorChainRule
import SafeLearning.CompleteBarrierNonlinearDomainComparison
import SafeLearning.CompleteBarrierControlAffine

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierDomainControl

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The nonlinear source comparison bound for the actual control-affine
trajectory, using alpha only on its stated interval J. -/
theorem genuine_control_affine_nonlinear_comparison
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U) (x : ℝ → E)
    (y alpha : ℝ → ℝ) (D : Set E) (J : Set ℝ) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hab : a ≤ b)
    (hm : MonotoneOn alpha J) (hx : AbsolutelyContinuousOnInterval x a b)
    (hy : AbsolutelyContinuousOnInterval y a b) (hxD : MapsTo x (uIcc a b) D)
    (heJ : MapsTo (h ∘ x) (Icc a b) J) (hyJ : MapsTo y (Icc a b) J)
    (hode : ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt x (f (x t) + g (x t) (u (x t))) t)
    (hyode : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt y (-alpha (y t)) t)
    (hcbf : ∀ z ∈ D, -alpha (h z) ≤
      fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z)))
    (h0 : y a ≤ h (x a)) : ∀ t ∈ Icc a b, y t ≤ h (x t) := by
  apply CompleteBarrierNonlinearDomainComparison.genuine_nonlinear_comparison
    (h ∘ x) (fun t => fderiv ℝ h (x t) (f (x t) + g (x t) (u (x t))))
    y alpha J a b hab hm
    (CompleteBarrierVectorChainRule.genuine_c1_ac_composition h x D a b hD hh hx hxD)
    hy heJ hyJ
    (CompleteBarrierVectorChainRule.genuine_ae_vector_chain_rule h x
      (fun t => f (x t) + g (x t) (u (x t))) D a b hD hh hab hxD hode)
    hyode _ h0
  exact Eventually.of_forall fun t ht => by
    rw [CompleteBarrierControlAffine.genuine_control_affine_lie_identity]
    exact hcbf (x t) (hxD (by simpa [uIcc_of_le hab] using ht))

/-- A concrete extended class-K alpha for which no exponential rate cancels
the nonlinear term identically. -/
theorem genuine_cubic_extended_classK :
    Continuous (fun r : ℝ => r ^ 3) ∧ StrictMono (fun r : ℝ => r ^ 3) ∧
      (fun r : ℝ => r ^ 3) 0 = 0 ∧
      ∀ beta : ℝ, ∃ r : ℝ, beta * r - r ^ 3 ≠ 0 := by
  refine ⟨by fun_prop, (by decide : Odd (3 : ℕ)).strictMono_pow, by norm_num, ?_⟩
  exact CompleteBarrierNonlinearDomainComparison.cubic_no_constant_factor_cancellation

end SafeLearning.CompleteBarrierDomainControl
