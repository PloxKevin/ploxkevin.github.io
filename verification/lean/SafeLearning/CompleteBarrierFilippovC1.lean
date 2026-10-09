import SafeLearning.CompleteBarrierFilippovHalfspaces
import SafeLearning.CompleteBarrierVectorChainRule

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SafeLearning.CompleteBarrierFilippovC1

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Continuous f,g and a locally bounded controller imply a locally bounded
actual control-affine velocity, even if the controller is discontinuous. -/
theorem genuine_local_control_affine_bound (f : E → E) (g : E → U →L[ℝ] E)
    (u : E → U) (x : E) (M : ℝ) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hu : ∀ᶠ z in 𝓝 x, ‖u z‖ ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝 x, ‖f z + g z (u z)‖ ≤ B := by
  have hf' : ∀ᶠ z in 𝓝 x, ‖f z‖ < ‖f x‖ + 1 :=
    hf.norm.eventually_lt_const (by linarith)
  have hg' : ∀ᶠ z in 𝓝 x, ‖g z‖ < ‖g x‖ + 1 :=
    hg.norm.eventually_lt_const (by linarith)
  refine ⟨‖f x‖ + 1 + (‖g x‖ + 1) * M, ?_⟩
  filter_upwards [hf', hg', hu] with z hf hg hu
  have hprod : ‖g z‖ * ‖u z‖ ≤ (‖g x‖ + 1) * M :=
    mul_le_mul hg.le hu (norm_nonneg _) (by positivity)
  exact (norm_add_le _ _).trans
    (add_le_add hf.le (((g z).le_opNorm (u z)).trans hprod))

/-- C1 regularity on the actual open domain supplies the continuous gradient
and threshold used in the essential closed convex velocity construction. -/
theorem genuine_c1_filippov_barrier [MeasurableSpace E] (mu : Measure E)
    (h : E → ℝ) (F : E → E) (D : Set E) (beta : ℝ) (x : E)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hx : x ∈ D)
    (hb : ∃ M : ℝ, ∀ᶠ z in 𝓝 x, ‖F z‖ ≤ M)
    (hcbf : ∀ z ∈ D, -beta * h z ≤ fderiv ℝ h z (F z))
    (v : E) (hv : v ∈ CompleteBarrierFilippovHalfspaces.velocities mu F x) :
    -beta * h x ≤ fderiv ℝ h x v := by
  obtain ⟨M, hb⟩ := hb
  have hp : ContinuousAt (fderiv ℝ h) x :=
    (hh.continuousOn_fderiv_of_isOpen hD le_rfl).continuousAt (hD.mem_nhds hx)
  have hq : ContinuousAt (fun z => -beta * h z) x :=
    (hh.continuousOn.continuousAt (hD.mem_nhds hx)).const_mul (-beta)
  have hDz : ∀ᶠ z in 𝓝 x, z ∈ D := hD.mem_nhds hx
  have hi : ∀ᶠ z in 𝓝 x, -beta * h z ≤ fderiv ℝ h z (F z) :=
    hDz.mono fun z hz => hcbf z hz
  exact CompleteBarrierFilippovHalfspaces.genuine_filippov_inequality_preservation
    mu F (fderiv ℝ h) (fun z => -beta * h z) x M hp hq hb hi v hv

/-- Every existing Filippov AC trajectory satisfies the same exponential
barrier bound, because all velocities of its inclusion satisfy the constraint. -/
theorem genuine_existing_filippov_solution_bound [MeasurableSpace E]
    (mu : Measure E) (h : E → ℝ) (F : E → E) (D : Set E) (beta T : ℝ)
    (x velocity : ℝ → E) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hT : 0 ≤ T) (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hxD : MapsTo x (uIcc 0 T) D)
    (hb : ∀ z ∈ D, ∃ M : ℝ, ∀ᶠ w in 𝓝 z, ‖F w‖ ≤ M)
    (hcbf : ∀ z ∈ D, -beta * h z ≤ fderiv ℝ h z (F z))
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (velocity t) t)
    (hv : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      velocity t ∈ CompleteBarrierFilippovHalfspaces.velocities mu F (x t)) :
    ∀ t ∈ Icc 0 T, h (x 0) * Real.exp (-beta * t) ≤ h (x t) := by
  apply CompleteBarrierVectorChainRule.genuine_vector_exponential_barrier
    h x velocity D beta T hD hh hT hx hxD hd
  filter_upwards [hv] with t hv ht
  have hz : x t ∈ D := hxD (by simpa [uIcc_of_le hT] using ht)
  exact genuine_c1_filippov_barrier mu h F D beta (x t) hD hh hz
    (hb (x t) hz) hcbf (velocity t) (hv ht)

end SafeLearning.CompleteBarrierFilippovC1
