import SafeLearning.CompleteAppliedBellmanReturns

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesViabilityFiniteDPCommonOptimizer30
open SafeLearning.CompleteAppliedBellman
  SafeLearning.CompleteAppliedBellmanReturns
  SafeLearning.CompleteFiniteCMDPOccupancy
  SafeLearning.CompleteFiniteHistoryPathLinearProgram
  SafeLearning.CompleteFiniteControlledPathMeasure
  SafeLearning.CompleteFiniteMarkovPathCorrespondence
  SafeLearning.CompleteFiniteCMDPDeterministicVertices

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- The controller is chosen before the initial law, so one stationary policy is optimal
simultaneously from every initial state and every initial probability law. -/
theorem actual_finite_discounted_DP_has_one_stationary_optimizer_for_every_initial_law
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ≥0) (hg : gamma < 1) :
    ∃ (value : S → ℝ) (feedback : S → A),
      (∀ s, bellman transition reward (gamma : ℝ) value s = value s) ∧
      ∀ initial : PMF S,
        pathReturn (actualPMFModel initial transition) (gamma : ℝ)
          (markovHistoryPolicy (purePolicy feedback)) reward = finiteMean initial value ∧
        ∀ policy : HistoryPolicy S A,
          pathReturn (actualPMFModel initial transition) (gamma : ℝ) policy reward ≤
            pathReturn (actualPMFModel initial transition) (gamma : ℝ)
              (markovHistoryPolicy (purePolicy feedback)) reward := by
  obtain ⟨value, hv, _, _⟩ :=
    bellman_fixed_point_exists_unique_and_iteration_converges transition reward gamma hg (fun _ => 0)
  refine ⟨value, greedyAction transition reward (gamma : ℝ) value, hv, ?_⟩
  intro initial
  have hgamma : (gamma : ℝ) < 1 := hg
  have he := actual_greedy_constructed_path_return_attains_the_bellman_value
    initial transition reward (gamma : ℝ) gamma.coe_nonneg hgamma value hv
  refine ⟨he, ?_⟩
  intro policy
  rw [he]
  exact actual_every_history_dependent_path_return_is_bounded_by_the_bellman_value
    initial transition reward (gamma : ℝ) gamma.coe_nonneg hgamma value hv policy

/-- Deterministic finite dynamics and penalized rewards are actual instances of the generic
finite discounted model, with no optimal-controller existence premise. -/
theorem actual_finite_deterministic_penalized_DP_common_stationary_optimizer
    (next : S → A → S) (reward failureCost : S → A → ℝ)
    (penalty : ℝ) (gamma : ℝ≥0) (hg : gamma < 1) :
    ∃ (value : S → ℝ) (feedback : S → A),
      ∀ initial : PMF S,
        pathReturn (actualPMFModel initial (fun s a => PMF.pure (next s a))) (gamma : ℝ)
          (markovHistoryPolicy (purePolicy feedback)) (fun s a => reward s a - penalty * failureCost s a) =
            finiteMean initial value ∧
        ∀ policy : HistoryPolicy S A,
          pathReturn (actualPMFModel initial (fun s a => PMF.pure (next s a))) (gamma : ℝ)
            policy (fun s a => reward s a - penalty * failureCost s a) ≤
          pathReturn (actualPMFModel initial (fun s a => PMF.pure (next s a))) (gamma : ℝ)
            (markovHistoryPolicy (purePolicy feedback))
            (fun s a => reward s a - penalty * failureCost s a) := by
  obtain ⟨value, feedback, _, h⟩ :=
    actual_finite_discounted_DP_has_one_stationary_optimizer_for_every_initial_law
      (fun s a => PMF.pure (next s a))
      (fun s a => reward s a - penalty * failureCost s a) gamma hg
  exact ⟨value, feedback, h⟩

end SafeLearning.CompleteModulesViabilityFiniteDPCommonOptimizer30
