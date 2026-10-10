import SafeLearning.CompleteFinitePolicyTrajectorySeries

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFinitePolicySeriesConsequences

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPInverse SafeLearning.CompleteFinitePolicyValues
  SafeLearning.CompleteFinitePolicyPerformance SafeLearning.CompleteFinitePolicyTrajectorySeries

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

theorem actual_initial_weighted_inverse_advantage_is_matrix_power_series
    (M : Model S A) (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    M.initial ⬝ᵥ ((discountedMatrix (policyKernel M π') γ)⁻¹ *ᵥ
      averagedAdvantage M π' γ r (policyValue M π γ r)) =
        ∑' n : ℕ, γ ^ n * ((M.initial ᵥ* (policyKernel M π') ^ n) ⬝ᵥ
          averagedAdvantage M π' γ r (policyValue M π γ r)) := by
  have h := actual_performance_difference_literal_matrix_power_series
    M π π' hw hw' γ hγ0 hγ1 r
  rw [actual_expected_return_equals_initial_value M π' hw' γ hγ0 hγ1 r,
    actual_expected_return_equals_initial_value M π hw γ hγ0 hγ1 r,
    ← dotProduct_sub, actual_value_difference_literal_inverse M π π' γ hγ0 hγ1 r] at h
  exact h

theorem actual_state_occupancy_is_matrix_power_series (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    policyStateOccupancy M π γ s =
      (1 - γ) * ∑' n : ℕ, γ ^ n * (M.initial ᵥ* (policyKernel M π) ^ n) s := by
  rw [policyStateOccupancy, stateMarginal,
    actual_occupancy_state_marginal M π γ hγ0 hγ1]
  congr 1
  apply tsum_congr
  intro n
  rw [actual_stationary_state_law_is_initial_times_matrix_power M π hw n]

theorem actual_state_occupancy_total_probability (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑ s, policyStateOccupancy M π γ s = 1 :=
  actual_all_feasible_flows_have_total_mass_one M γ hγ1 (occupancy M π γ)
    (actual_occupancy_satisfies_flow M π γ hγ0 hγ1)

theorem actual_constant_advantage_distribution_error_zero (M : Model S A)
    (π π' : Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : ℝ) :
    (policyStateOccupancy M π' γ - policyStateOccupancy M π γ) ⬝ᵥ
      (fun _ => c) = 0 := by
  simp only [dotProduct, Pi.sub_apply]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    actual_state_occupancy_total_probability M π' γ hγ0 hγ1,
    actual_state_occupancy_total_probability M π γ hγ0 hγ1]
  ring

theorem actual_constant_advantage_surrogate_is_exact (M : Model S A) (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) (c : ℝ)
    (hc : ∀ s, averagedAdvantage M π' γ r (policyValue M π γ r) s = c) :
    expectedReturn M π' γ r - expectedReturn M π γ r =
      (policyStateOccupancy M π γ ⬝ᵥ
        averagedAdvantage M π' γ r (policyValue M π γ r)) / (1 - γ) := by
  rw [actual_expected_performance_difference M π π' hw hw' γ hγ0 hγ1 r]
  congr 1
  have h := actual_constant_advantage_distribution_error_zero M π π' γ hγ0 hγ1 c
  rw [sub_dotProduct] at h
  have he : averagedAdvantage M π' γ r (policyValue M π γ r) = fun _ => c := funext hc
  rw [he]
  exact sub_eq_zero.mp h

end SafeLearning.CompleteFinitePolicySeriesConsequences
