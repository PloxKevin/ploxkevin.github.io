import SafeLearning.CompleteBarrierVectorChainRule

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierControlAffine

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The actual control-affine velocity produces exactly the two Lie derivatives
in the barrier constraint. -/
theorem genuine_control_affine_lie_identity (h : E → ℝ) (f : E → E)
    (g : E → U →L[ℝ] E) (u : E → U) (z : E) :
    fderiv ℝ h z (f z + g z (u z)) =
      fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z)) := by
  exact map_add _ _ _

/-- The source CBF membership condition gives the exponential lower bound for
every existing control-affine AC solution that remains in the C1 domain. -/
theorem genuine_control_affine_exponential_bound
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U) (x : ℝ → E)
    (D : Set E) (beta T : ℝ) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hT : 0 ≤ T) (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hxD : MapsTo x (uIcc 0 T) D)
    (hode : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt x (f (x t) + g (x t) (u (x t))) t)
    (hcbf : ∀ z ∈ D, -beta * h z ≤
      fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z))) :
    ∀ t ∈ Icc 0 T, h (x 0) * Real.exp (-beta * t) ≤ h (x t) := by
  apply CompleteBarrierVectorChainRule.genuine_vector_exponential_barrier
    h x (fun t => f (x t) + g (x t) (u (x t))) D beta T hD hh hT hx hxD hode
  exact Eventually.of_forall fun t ht => by
    rw [genuine_control_affine_lie_identity]
    exact hcbf (x t) (hxD (by simpa [uIcc_of_le hT] using ht))

theorem genuine_control_affine_safety
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U) (x : ℝ → E)
    (D : Set E) (beta T : ℝ) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hT : 0 ≤ T) (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hxD : MapsTo x (uIcc 0 T) D)
    (hode : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt x (f (x t) + g (x t) (u (x t))) t)
    (hcbf : ∀ z ∈ D, -beta * h z ≤
      fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z)))
    (h0 : 0 ≤ h (x 0)) : ∀ t ∈ Icc 0 T, 0 ≤ h (x t) := by
  intro t ht
  exact (mul_nonneg h0 (Real.exp_pos _).le).trans
    (genuine_control_affine_exponential_bound h f g u x D beta T hD hh hT hx hxD hode hcbf t ht)

end SafeLearning.CompleteBarrierControlAffine
