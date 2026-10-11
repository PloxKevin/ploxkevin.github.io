import SafeLearning.CompleteFinitePolicyExample
import SafeLearning.CompleteFinitePolicySeriesConsequences

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFinitePolicySurrogateConsequences

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPInverse
  SafeLearning.CompleteFinitePolicyValues SafeLearning.CompleteFinitePolicyPerformance
  SafeLearning.CompleteFinitePolicyExample

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

theorem actual_surrogate_error_is_distribution_difference (M : Model S A)
    (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    expectedReturn M π' γ r - expectedReturn M π γ r -
        (policyStateOccupancy M π γ ⬝ᵥ
          averagedAdvantage M π' γ r (policyValue M π γ r)) / (1 - γ) =
      ((policyStateOccupancy M π' γ - policyStateOccupancy M π γ) ⬝ᵥ
        averagedAdvantage M π' γ r (policyValue M π γ r)) / (1 - γ) := by
  rw [actual_expected_performance_difference M π π' hw hw' γ hγ0 hγ1 r,
    sub_dotProduct, sub_div]

theorem actual_improving_chain_initial_state (s : State) :
    stateMass model improvingPolicy 0 s = if s = 0 then 1 else 0 := rfl

theorem actual_improving_chain_all_positive_times (n : ℕ) (s : State) :
    stateMass model improvingPolicy (n + 1) s = if s = 1 then 1 else 0 := by
  have h := actual_state_total_mass model improvingPolicy n
  fin_cases s
  · norm_num [stateMass, model, improvingPolicy, nextState, Fin.sum_univ_two]
  · simpa [stateMass, model, improvingPolicy, nextState, Fin.sum_univ_two] using h

theorem actual_example_literal_inverse_advantage :
    (discountedMatrix (policyKernel model improvingPolicy) (1 / 2))⁻¹ *ᵥ
      averagedAdvantage model improvingPolicy (1 / 2) reward
        (policyValue model randomPolicy (1 / 2) reward) = fun _ => 1 / 2 := by
  rw [← actual_value_difference_literal_inverse model randomPolicy improvingPolicy
      (1 / 2) (by norm_num) (by norm_num) reward,
    actual_improving_inverse_value, actual_random_inverse_value]
  funext s
  fin_cases s <;> norm_num [newValue, oldValue]

end SafeLearning.CompleteFinitePolicySurrogateConsequences
