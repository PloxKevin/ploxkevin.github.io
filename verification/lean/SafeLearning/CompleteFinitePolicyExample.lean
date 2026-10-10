import SafeLearning.CompleteFinitePolicyPerformance

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFinitePolicyExample

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPRecovery
  SafeLearning.CompleteFinitePolicyValues SafeLearning.CompleteFinitePolicyPerformance

abbrev State := Fin 2
abbrev Action := Fin 2

/-- Action zero stays; action one switches to the other state. -/
def nextState (s : State) (a : Action) : State :=
  if a = 0 then s else if s = 0 then 1 else 0

def model : Model State Action where
  initial s := if s = 0 then 1 else 0
  transition s a t := if t = nextState s a then 1 else 0
  initial_nonneg s := by split_ifs <;> norm_num
  initial_sum := by norm_num [Fin.sum_univ_two]
  transition_nonneg s a t := by split_ifs <;> norm_num
  transition_sum s a := by simp

def randomPolicy : Policy State Action where
  action _ _ _ := 1 / 2
  action_nonneg _ _ _ := by norm_num
  action_sum _ _ := by norm_num [Fin.sum_univ_two]

def improvingPolicy : Policy State Action where
  action _ s a := if a = (if s = 0 then 1 else 0) then 1 else 0
  action_nonneg _ s a := by split_ifs <;> norm_num
  action_sum _ s := by simp

def reward (s : State) (_ : Action) : ℝ := if s = 0 then 0 else 1
def oldValue (s : State) : ℝ := if s = 0 then 1 / 2 else 3 / 2
def newValue (s : State) : ℝ := if s = 0 then 1 else 2
def oldOccupancy (s : State) : ℝ := if s = 0 then 3 / 4 else 1 / 4
def newOccupancy (_ : State) : ℝ := 1 / 2

theorem random_policy_stationary (n : ℕ) (s : State) (a : Action) :
    randomPolicy.action n s a = randomPolicy.action 0 s a := rfl

theorem improving_policy_stationary (n : ℕ) (s : State) (a : Action) :
    improvingPolicy.action n s a = improvingPolicy.action 0 s a := rfl

theorem actual_random_kernel (s t : State) : policyKernel model randomPolicy s t = 1 / 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [policyKernel, stationaryKernel, model, randomPolicy, nextState, Fin.sum_univ_two]

theorem actual_improving_kernel (s t : State) :
    policyKernel model improvingPolicy s t = if t = 1 then 1 else 0 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [policyKernel, stationaryKernel, model, improvingPolicy, nextState,
      Fin.sum_univ_two]

theorem actual_random_inverse_value : policyValue model randomPolicy (1 / 2) reward = oldValue := by
  symm
  apply actual_bellman_solution_is_inverse_value model randomPolicy (1 / 2)
    (by norm_num) (by norm_num)
  intro s
  simp only [Matrix.mulVec, dotProduct, actual_random_kernel]
  fin_cases s <;>
    norm_num [policyReward, randomPolicy, reward, Matrix.mulVec, dotProduct,
      actual_random_kernel, oldValue, Fin.sum_univ_two]

theorem actual_improving_inverse_value :
    policyValue model improvingPolicy (1 / 2) reward = newValue := by
  symm
  apply actual_bellman_solution_is_inverse_value model improvingPolicy (1 / 2)
    (by norm_num) (by norm_num)
  intro s
  simp only [Matrix.mulVec, dotProduct, actual_improving_kernel]
  fin_cases s <;>
    norm_num [policyReward, improvingPolicy, reward, Matrix.mulVec, dotProduct,
      actual_improving_kernel, newValue, Fin.sum_univ_two]

theorem actual_action_values (s : State) (a : Action) :
    actionValue model (1 / 2) reward (policyValue model randomPolicy (1 / 2) reward) s a =
      if s = 0 then (if a = 0 then 1 / 4 else 3 / 4)
      else (if a = 0 then 7 / 4 else 5 / 4) := by
  rw [actual_random_inverse_value]
  fin_cases s <;> fin_cases a <;>
    norm_num [actionValue, model, nextState, oldValue, reward, Fin.sum_univ_two]

theorem actual_action_advantages (s : State) (a : Action) :
    actionAdvantage model (1 / 2) reward (policyValue model randomPolicy (1 / 2) reward) s a =
      if s = 0 then (if a = 0 then -(1 / 4) else 1 / 4)
      else (if a = 0 then 1 / 4 else -(1 / 4)) := by
  simp only [actionAdvantage, actual_action_values]
  rw [actual_random_inverse_value]
  fin_cases s <;> fin_cases a <;> norm_num [oldValue]

theorem actual_averaged_advantage (s : State) :
    averagedAdvantage model improvingPolicy (1 / 2) reward
      (policyValue model randomPolicy (1 / 2) reward) s = 1 / 4 := by
  simp only [averagedAdvantage, actual_action_advantages]
  fin_cases s <;> norm_num [improvingPolicy, Fin.sum_univ_two]

theorem actual_random_state_occupancy :
    policyStateOccupancy model randomPolicy (1 / 2) = oldOccupancy := by
  have hK := actual_policy_kernel_probability_law model randomPolicy
  apply actual_stochastic_discounted_fixed_point_unique
    (policyKernel model randomPolicy) hK.1 hK.2 (1 / 2)
    (by norm_num) (by norm_num) model.initial
  · exact actual_stationary_state_occupancy_fixed_point model randomPolicy
      random_policy_stationary (1 / 2) (by norm_num) (by norm_num)
  · intro s
    simp only [actual_random_kernel]
    fin_cases s <;> norm_num [model, oldOccupancy, actual_random_kernel, Fin.sum_univ_two]

theorem actual_improving_state_occupancy :
    policyStateOccupancy model improvingPolicy (1 / 2) = newOccupancy := by
  have hK := actual_policy_kernel_probability_law model improvingPolicy
  apply actual_stochastic_discounted_fixed_point_unique
    (policyKernel model improvingPolicy) hK.1 hK.2 (1 / 2)
    (by norm_num) (by norm_num) model.initial
  · exact actual_stationary_state_occupancy_fixed_point model improvingPolicy
      improving_policy_stationary (1 / 2) (by norm_num) (by norm_num)
  · intro s
    simp only [actual_improving_kernel]
    fin_cases s <;> norm_num [model, newOccupancy, actual_improving_kernel, Fin.sum_univ_two]

theorem actual_policy_returns :
    expectedReturn model randomPolicy (1 / 2) reward = 1 / 2 ∧
    expectedReturn model improvingPolicy (1 / 2) reward = 1 := by
  rw [actual_expected_return_equals_initial_value model randomPolicy random_policy_stationary
    (1 / 2) (by norm_num) (by norm_num),
    actual_expected_return_equals_initial_value model improvingPolicy improving_policy_stationary
      (1 / 2) (by norm_num) (by norm_num),
    actual_random_inverse_value, actual_improving_inverse_value]
  norm_num [dotProduct, model, oldValue, newValue, Fin.sum_univ_two]

theorem actual_performance_difference_check :
    expectedReturn model improvingPolicy (1 / 2) reward -
      expectedReturn model randomPolicy (1 / 2) reward =
        (policyStateOccupancy model improvingPolicy (1 / 2) ⬝ᵥ
          averagedAdvantage model improvingPolicy (1 / 2) reward
            (policyValue model randomPolicy (1 / 2) reward)) / (1 - 1 / 2) ∧
    expectedReturn model improvingPolicy (1 / 2) reward -
      expectedReturn model randomPolicy (1 / 2) reward = 1 / 2 := by
  constructor
  · exact actual_expected_performance_difference model randomPolicy improvingPolicy
      random_policy_stationary improving_policy_stationary (1 / 2)
      (by norm_num) (by norm_num) reward
  · rw [actual_policy_returns.1, actual_policy_returns.2]
    norm_num

theorem actual_old_state_surrogate_is_exact :
    (policyStateOccupancy model randomPolicy (1 / 2) ⬝ᵥ
      averagedAdvantage model improvingPolicy (1 / 2) reward
        (policyValue model randomPolicy (1 / 2) reward)) / (1 - 1 / 2) = 1 / 2 := by
  rw [actual_random_state_occupancy]
  norm_num [dotProduct, actual_averaged_advantage, oldOccupancy, Fin.sum_univ_two]

theorem actual_constant_advantage_error_vanishes :
    ((policyStateOccupancy model improvingPolicy (1 / 2) -
        policyStateOccupancy model randomPolicy (1 / 2)) ⬝ᵥ
      averagedAdvantage model improvingPolicy (1 / 2) reward
        (policyValue model randomPolicy (1 / 2) reward)) / (1 - 1 / 2) = 0 := by
  rw [actual_random_state_occupancy, actual_improving_state_occupancy]
  norm_num [dotProduct, actual_averaged_advantage, oldOccupancy, newOccupancy,
    Fin.sum_univ_two]

end SafeLearning.CompleteFinitePolicyExample
