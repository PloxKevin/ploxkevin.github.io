import SafeLearning.CompleteAppliedBellmanReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace SafeLearning.CompleteAppliedOptimalValue
open CompleteAppliedBellman CompleteAppliedBellmanReturns
open CompleteFiniteHistoryPathLinearProgram CompleteFiniteControlledPathMeasure
open CompleteFiniteMarkovPathCorrespondence CompleteFiniteCMDPDeterministicVertices

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

def optimalValue (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) : S → ℝ :=
  Classical.choose (bellman_fixed_point_exists_unique_and_iteration_converges
    transition reward gamma hg (fun _ => 0))

theorem actual_optimal_value_is_a_derived_unique_bellman_fixed_point
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) :
    (∀ s,bellman transition reward (gamma:ℝ) (optimalValue transition reward gamma hg) s=
      optimalValue transition reward gamma hg s) ∧
    (∀ other : S → ℝ,(∀ s,bellman transition reward (gamma:ℝ) other s=other s) →
      other=optimalValue transition reward gamma hg) := by
  have h := Classical.choose_spec (bellman_fixed_point_exists_unique_and_iteration_converges
    transition reward gamma hg (fun _ => 0))
  exact ⟨h.1,h.2.2⟩

variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

def optimalPathReturn (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (s : S) : ℝ :=
  sSup {v : ℝ | ∃ pi : HistoryPolicy S A,
    pathReturn (actualPMFModel (PMF.pure s) transition) gamma pi reward=v}

theorem actual_pure_initial_mean_is_the_value_at_that_state (value : S → ℝ) (s : S) :
    finiteMean (PMF.pure s) value=value s := by
  classical
  unfold finiteMean
  rw [Finset.sum_eq_single s]
  · simp [PMF.pure_apply]
  · intro t ht hne
    simp [PMF.pure_apply,hne]
  · simp

theorem actual_all_history_path_returns_have_an_attained_greedy_optimum_at_each_state
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) (s : S) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy S A,
      pathReturn (actualPMFModel (PMF.pure s) transition) (gamma:ℝ) pi reward=v}
        (optimalValue transition reward gamma hg s) := by
  have h := actual_bellman_fixed_point_is_the_attained_optimum_over_all_history_paths
    (PMF.pure s) transition reward (gamma:ℝ) gamma.coe_nonneg
    (by exact_mod_cast hg) (optimalValue transition reward gamma hg)
    (actual_optimal_value_is_a_derived_unique_bellman_fixed_point transition reward gamma hg).1
  rwa [actual_pure_initial_mean_is_the_value_at_that_state] at h

theorem actual_optimal_trajectory_return_equals_the_derived_bellman_value
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) :
    optimalPathReturn transition reward (gamma:ℝ)=optimalValue transition reward gamma hg := by
  funext s
  exact (actual_all_history_path_returns_have_an_attained_greedy_optimum_at_each_state
    transition reward gamma hg s).csSup_eq

theorem actual_greedy_constructed_path_from_each_state_attains_the_optimal_value
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) (s : S) :
    pathReturn (actualPMFModel (PMF.pure s) transition) (gamma:ℝ)
      (markovHistoryPolicy (purePolicy
        (greedyAction transition reward (gamma:ℝ) (optimalValue transition reward gamma hg)))) reward=
      optimalPathReturn transition reward (gamma:ℝ) s := by
  rw [actual_optimal_trajectory_return_equals_the_derived_bellman_value]
  have h := actual_greedy_constructed_path_return_attains_the_bellman_value
    (PMF.pure s) transition reward (gamma:ℝ) gamma.coe_nonneg
    (by exact_mod_cast hg) (optimalValue transition reward gamma hg)
    (actual_optimal_value_is_a_derived_unique_bellman_fixed_point transition reward gamma hg).1
  rwa [actual_pure_initial_mean_is_the_value_at_that_state] at h

variable [Nonempty S]

theorem actual_residual_bounds_error_to_true_optimal_trajectory_returns
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma<1) (candidate : S → ℝ) (residual : ℝ)
    (hr : valueNorm (fun s => bellman transition reward (gamma:ℝ) candidate s-candidate s)≤residual) :
    valueNorm (fun s => candidate s-optimalPathReturn transition reward (gamma:ℝ) s)≤
      residual/(1-(gamma:ℝ)) := by
  rw [actual_optimal_trajectory_return_equals_the_derived_bellman_value transition reward gamma hg]
  exact bellman_residual_error transition reward (gamma:ℝ) residual gamma.coe_nonneg
    (by exact_mod_cast hg) candidate (optimalValue transition reward gamma hg)
    (actual_optimal_value_is_a_derived_unique_bellman_fixed_point transition reward gamma hg).1 hr

theorem actual_source_point_zero_three_residual_bounds_the_true_optimal_value_error
    (transition : S → A → PMF S) (reward : S → A → ℝ) (candidate : S → ℝ)
    (hr : valueNorm (fun s => bellman transition reward (9/10) candidate s-candidate s)=3/100) :
    valueNorm (fun s => candidate s-optimalPathReturn transition reward (9/10) s)≤3/10 := by
  have h := actual_residual_bounds_error_to_true_optimal_trajectory_returns transition reward
    (9/10:ℝ≥0) (by norm_num) candidate (3/100) (by exact hr.le)
  norm_num at h
  exact h

theorem actual_source_point_zero_one_residual_guarantees_point_one_optimal_value_error
    (transition : S → A → PMF S) (reward : S → A → ℝ) (candidate : S → ℝ)
    (hr : valueNorm (fun s => bellman transition reward (9/10) candidate s-candidate s)≤1/100) :
    valueNorm (fun s => candidate s-optimalPathReturn transition reward (9/10) s)≤1/10 := by
  have h := actual_residual_bounds_error_to_true_optimal_trajectory_returns transition reward
    (9/10:ℝ≥0) (by norm_num) candidate (1/100) hr
  norm_num at h
  exact h

end SafeLearning.CompleteAppliedOptimalValue
