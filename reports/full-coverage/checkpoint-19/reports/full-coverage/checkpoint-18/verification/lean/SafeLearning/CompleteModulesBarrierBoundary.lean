import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped Topology
namespace SafeLearning.CompleteModulesBarrierBoundary

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem actual_determinant_tends_to_zero_at_finite_singular_boundary
    {T : Type*} (filter : Filter T) (matrix : T → Matrix N N ℝ)
    (boundary : Matrix N N ℝ) (hboundary : boundary.det=0)
    (hconvergence : Tendsto matrix filter (𝓝 boundary)) :
    Tendsto (fun t => (matrix t).det) filter (𝓝 0) := by
  have hcontinuous : Continuous (fun value : Matrix N N ℝ => value.det) := continuous_id.matrix_det
  have h := (hcontinuous.tendsto boundary).comp hconvergence
  simpa only [hboundary,Function.comp_def] using h

theorem actual_logdet_barrier_blows_up_at_finite_singular_boundary
    {T : Type*} (filter : Filter T) (matrix : T → Matrix N N ℝ)
    (boundary : Matrix N N ℝ) (hboundary : boundary.det=0)
    (hconvergence : Tendsto matrix filter (𝓝 boundary))
    (hpositive : ∀ t, (matrix t).PosDef) (mu : ℝ) (hmu : 0 < mu) :
    Tendsto (fun t => -mu*Real.log (matrix t).det) filter atTop := by
  have hdet : Tendsto (fun t => (matrix t).det) filter (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨actual_determinant_tends_to_zero_at_finite_singular_boundary
      filter matrix boundary hboundary hconvergence,
      Eventually.of_forall (fun t => (hpositive t).det_pos)⟩
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hdet
  have hneg := tendsto_neg_atBot_atTop.comp hlog
  have h := (tendsto_const_mul_atTop_of_pos hmu).mpr hneg
  simpa [Function.comp_def,neg_mul,mul_neg] using h

theorem actual_logdet_barrier_blows_up_at_noninvertible_finite_boundary
    {T : Type*} (filter : Filter T) (matrix : T → Matrix N N ℝ)
    (boundary : Matrix N N ℝ) (hsingular : ¬IsUnit boundary)
    (hconvergence : Tendsto matrix filter (𝓝 boundary))
    (hpositive : ∀ t, (matrix t).PosDef) (mu : ℝ) (hmu : 0 < mu) :
    Tendsto (fun t => -mu*Real.log (matrix t).det) filter atTop := by
  have hdet : boundary.det=0 := by
    by_contra hnonzero
    exact hsingular (boundary.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hnonzero))
  exact actual_logdet_barrier_blows_up_at_finite_singular_boundary
    filter matrix boundary hdet hconvergence hpositive mu hmu

end SafeLearning.CompleteModulesBarrierBoundary
