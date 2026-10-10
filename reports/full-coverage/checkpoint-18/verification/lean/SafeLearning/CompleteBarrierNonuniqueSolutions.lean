import Mathlib

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteBarrierNonuniqueSolutions

/-- A continuous, hence measurable, controller for f=0 and g=1. It need not
be locally Lipschitz, as its two genuine solutions from zero will show. -/
def field (x : ℝ) : ℝ := 2 * Real.sqrt (max x 0)

theorem genuine_continuous_field : Continuous field := by
  unfold field
  fun_prop

theorem genuine_measurable_field : Measurable field := genuine_continuous_field.measurable

theorem stationary_solution (t : ℝ) :
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) (field 0) t := by
  simpa [field] using hasDerivAt_const t (0 : ℝ)

theorem moving_solution (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => s ^ 2) (field (t ^ 2)) t := by
  have hs : field (t ^ 2) = 2 * t := by
    simp [field, max_eq_left (sq_nonneg t), Real.sqrt_sq ht]
  rw [hs]
  convert (hasDerivAt_id t).pow 2 using 1 <;> try simp
  rfl

theorem genuine_two_distinct_ac_solutions (T : ℝ) (hT : 0 < T) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) 0 T ∧
    AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ 2) 0 T ∧
    (fun _ : ℝ => (0 : ℝ)) 0 = (fun t : ℝ => t ^ 2) 0 ∧
    (∀ t ∈ Icc 0 T, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (field 0) t) ∧
    (∀ t ∈ Icc 0 T, HasDerivAt (fun s : ℝ => s ^ 2) (field (t ^ 2)) t) ∧
    (fun _ : ℝ => (0 : ℝ)) T ≠ (fun t : ℝ => t ^ 2) T := by
  have hz : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hsq : AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ 2) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  refine ⟨hz, hsq, by simp, fun t _ => stationary_solution t,
    fun t ht => moving_solution t ht.1, ?_⟩
  exact (pow_pos hT 2).ne

end SafeLearning.CompleteBarrierNonuniqueSolutions
