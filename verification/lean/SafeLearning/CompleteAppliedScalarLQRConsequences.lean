import SafeLearning.CompleteAppliedScalarLQR
import SafeLearning.CompleteAppliedScalarODEBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarLQRConsequences
open CompleteAppliedScalarLQR CompleteAppliedScalarODE CompleteAppliedScalarODEBridges

def actualFiniteCostClassicalPairs (initial : ℝ) : Set ((ℝ→ℝ)×(ℝ→ℝ)) :=
  {pair | pair.1 0=initial ∧
    (∀time∈Ici (0:ℝ),HasDerivAt pair.1 (pair.1 time+pair.2 time) time) ∧
    MemLp pair.1 2 (volume.restrict (Ioi (0:ℝ))) ∧
    MemLp pair.2 2 (volume.restrict (Ioi (0:ℝ)))}

def actualSourceCost (pair : (ℝ→ℝ)×(ℝ→ℝ)) : ℝ :=
  ∫time in Ioi (0:ℝ),pair.1 time^2+pair.2 time^2

theorem actual_source_value_is_the_attained_global_minimum_of_all_finite_cost_classical_pairs
    (initial : ℝ) :
    IsLeast (actualSourceCost '' actualFiniteCostClassicalPairs initial) (sourceP*initial^2) := by
  have ht := actual_optimal_feedback_trajectory_has_the_true_ode_and_exponential_decay initial
  have hs := actual_optimal_feedback_trajectory_has_square_integrable_state_and_input initial
  constructor
  · refine ⟨(sourceTrajectory initial,sourceInput initial),⟨ht.1,fun time _=>ht.2.1 time,hs⟩,?_⟩
    exact actual_feedback_attains_the_true_infinite_horizon_cost initial
  · rintro cost ⟨pair,⟨hzero,hode,hstate,hinput⟩,rfl⟩
    have hl := actual_all_finite_cost_classical_controls_have_cost_at_least_the_derived_value
      pair.1 pair.2 hode hstate hinput
    simpa [actualSourceCost,hzero] using hl

theorem actual_positive_value_function_and_stabilizing_closed_loop_rate :
    (∀state : ℝ,state≠0 → 0<sourceP*state^2) ∧
      (1-sourceP= -Real.sqrt 2) ∧ (1-sourceP<0) ∧
      (1-(1-Real.sqrt 2)=Real.sqrt 2) ∧ (0<1-(1-Real.sqrt 2)) := by
  have hs := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  refine ⟨fun state hstate=>mul_pos
    actual_source_riccati_roots_positive_choice_and_rounding.2.1 (sq_pos_of_ne_zero hstate),?_,?_,?_,?_⟩
  · unfold sourceP;ring
  · unfold sourceP;linarith
  · ring
  · linarith

theorem actual_negative_riccati_root_has_a_growing_closed_loop
    (initial : ℝ) (hinitial : initial≠0) :
    (∀time : ℝ,HasDerivAt (solution (1-(1-Real.sqrt 2)) initial)
      ((1-(1-Real.sqrt 2))*solution (1-(1-Real.sqrt 2)) initial time) time) ∧
      Tendsto (fun time=>|solution (1-(1-Real.sqrt 2)) initial time|) atTop atTop := by
  exact ⟨actual_linear_solution_ODE _ initial,
    actual_positive_rate_all_nonzero_magnitudes_grow _ initial
      actual_positive_value_function_and_stabilizing_closed_loop_rate.2.2.2.2 hinitial⟩

end SafeLearning.CompleteAppliedScalarLQRConsequences
