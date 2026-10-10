import SafeLearning.CompleteCompactLyapunov
import SafeLearning.CompleteLyapunovCounterexample

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsNonlinearDecreasingModel

def sourceMap (x : ℝ) : ℝ := x/(1+x^2)
def sourceValue (x : ℝ) : ℝ := x^2
def sourceOrbit : ℕ → ℝ
  | 0 => 1
  | n+1 => sourceMap (sourceOrbit n)

theorem actual_source_map_is_continuous_and_fixes_zero :
    Continuous sourceMap ∧ sourceMap 0=0 := by
  constructor
  · unfold sourceMap
    exact continuous_id.div (continuous_const.add (continuous_id.pow 2))
      (fun x => ne_of_gt (by positivity))
  · norm_num [sourceMap]

theorem actual_square_value_is_continuous_nonnegative_with_every_compact_sublevel :
    Continuous sourceValue ∧ sourceValue 0=0 ∧
      (∀x:ℝ,0 ≤ sourceValue x) ∧
      (∀c:ℝ,IsCompact {x:ℝ | sourceValue x ≤ c}) := by
  exact ⟨continuous_id.pow 2,by norm_num [sourceValue],sq_nonneg,
    CompleteLyapunovCounterexample.all_square_sublevels_compact⟩

theorem actual_square_value_strictly_decreases_at_every_nonzero_state
    (x : ℝ) (hx : x≠0) : sourceValue (sourceMap x)<sourceValue x := by
  have hs : 0<x^2 := sq_pos_of_ne_zero hx
  have hd : 1<(1+x^2)^2 := by nlinarith [sq_nonneg (x^2)]
  have hm := mul_lt_mul_of_pos_left hd hs
  unfold sourceValue sourceMap
  rw [div_pow]
  apply (div_lt_iff₀ (by positivity : 0<(1+x^2)^2)).mpr
  simpa only [mul_one] using hm

theorem actual_every_source_recurrence_from_every_initial_state_converges_to_zero
    (state : ℕ→ℝ) (hstep : ∀n,state (n+1)=sourceMap (state n)) :
    Tendsto state atTop (𝓝 0) ∧
      Tendsto (fun n=>sourceValue (state n)) atTop (𝓝 0) := by
  have hm := actual_source_map_is_continuous_and_fixes_zero
  have hv := actual_square_value_is_continuous_nonnegative_with_every_compact_sublevel
  have hd : ∀x:ℝ,sourceValue x ≤ sourceValue (state 0) → x≠0 →
      sourceValue (sourceMap x)<sourceValue x := fun x _ hx =>
    actual_square_value_strictly_decreases_at_every_nonzero_state x hx
  exact ⟨CompleteCompactLyapunov.compact_strict_lyapunov_convergence
    sourceMap sourceValue state (sourceValue (state 0)) hm.1 hv.1
    (hv.2.2.2 _) hv.2.2.1 hm.2 hstep le_rfl hd,
    CompleteCompactLyapunov.actual_lyapunov_values_converge_to_zero
      sourceMap sourceValue state (sourceValue (state 0)) hm.1 hv.1
      (hv.2.2.2 _) hv.2.2.1 hv.2.1 hm.2 hstep le_rfl hd⟩

theorem actual_source_orbit_is_positive_at_every_natural_time :
    ∀n:ℕ,0<sourceOrbit n := by
  intro n
  induction n with
  | zero => norm_num [sourceOrbit]
  | succ n ih =>
    rw [sourceOrbit,sourceMap]
    exact div_pos ih (by positivity)

theorem actual_source_values_strictly_decrease_and_converge_to_zero :
    (∀n:ℕ,sourceValue (sourceOrbit (n+1))<sourceValue (sourceOrbit n)) ∧
      Tendsto sourceOrbit atTop (𝓝 0) ∧
      Tendsto (fun n=>sourceValue (sourceOrbit n)) atTop (𝓝 0) := by
  refine ⟨?_,actual_every_source_recurrence_from_every_initial_state_converges_to_zero
    sourceOrbit (fun _=>rfl)⟩
  intro n
  exact actual_square_value_strictly_decreases_at_every_nonzero_state _
    (actual_source_orbit_is_positive_at_every_natural_time n).ne'

theorem actual_first_five_source_states_and_square_values :
    sourceOrbit 0=1 ∧ sourceOrbit 1=1/2 ∧ sourceOrbit 2=2/5 ∧
      sourceOrbit 3=10/29 ∧ sourceOrbit 4=290/941 ∧
      sourceValue (sourceOrbit 0)=1 ∧ sourceValue (sourceOrbit 1)=1/4 ∧
      sourceValue (sourceOrbit 2)=4/25 ∧ sourceValue (sourceOrbit 3)=100/841 ∧
      sourceValue (sourceOrbit 4)=84100/885481 := by
  norm_num [sourceOrbit,sourceMap,sourceValue]

theorem actual_three_decimal_display_roundings_of_the_last_two_values :
    |sourceValue (sourceOrbit 3)-119/1000|<1/2000 ∧
      |sourceValue (sourceOrbit 4)-95/1000|<1/2000 ∧
      sourceValue (sourceOrbit 3)≠119/1000 ∧
      sourceValue (sourceOrbit 4)≠95/1000 := by
  norm_num [sourceOrbit,sourceMap,sourceValue]

end SafeLearning.CompleteFoundationsNonlinearDecreasingModel
