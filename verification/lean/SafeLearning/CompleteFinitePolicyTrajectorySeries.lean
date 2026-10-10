import SafeLearning.CompleteFinitePolicyPerformance
import SafeLearning.CompleteFinitePolicyNeumann

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace SafeLearning.CompleteFinitePolicyTrajectorySeries

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPRecovery
  SafeLearning.CompleteFiniteCMDPInverse SafeLearning.CompleteFinitePolicyValues
  SafeLearning.CompleteFinitePolicyPerformance SafeLearning.CompleteFinitePolicyNeumann

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

local instance : MetricSpace (Matrix S S ℝ) :=
  @NormedRing.toMetricSpace (Matrix S S ℝ) Matrix.linftyOpNormedRing
local instance : UniformSpace (Matrix S S ℝ) := PseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace (Matrix S S ℝ) := UniformSpace.toTopologicalSpace

theorem actual_normalized_initial_law_has_nonempty_states (M : Model S A) : Nonempty S := by
  classical
  by_contra h
  haveI : IsEmpty S := not_nonempty_iff.mp h
  have hz : (∑ s, M.initial s) = 0 := by simp
  linarith [M.initial_sum]

theorem actual_stationary_policy_matrix_neumann_inverse (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (discountedMatrix (policyKernel M π) γ)⁻¹ =
      ∑' n : ℕ, γ ^ n • (policyKernel M π) ^ n := by
  letI : Nonempty S := actual_normalized_initial_law_has_nonempty_states M
  have hK := actual_policy_kernel_probability_law M π
  exact actual_literal_neumann_inverse (policyKernel M π) hK.1 hK.2 γ hγ0 hγ1

theorem actual_stationary_state_law_is_initial_times_matrix_power (M : Model S A)
    (π : Policy S A) (hw : ∀ n s a, π.action n s a = π.action 0 s a) (n : ℕ) :
    stateMass M π n = M.initial ᵥ* (policyKernel M π) ^ n := by
  induction n with
  | zero => simp [stateMass]
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ← ih]
    ext t
    simp only [stateMass, policyKernel, stationaryKernel, Matrix.vecMul, dotProduct,
      Finset.mul_sum, mul_assoc, hw]

theorem actual_state_only_return_is_matrix_power_series (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (v : S → ℝ) :
    expectedReturn M π γ (fun s _ => v s) =
      ∑' n : ℕ, γ ^ n * ((M.initial ᵥ* (policyKernel M π) ^ n) ⬝ᵥ v) := by
  simp only [expectedReturn]
  apply tsum_congr
  intro n
  congr 1
  simp only [← Finset.sum_mul, actual_joint_state_marginal]
  rw [actual_stationary_state_law_is_initial_times_matrix_power M π hw n]
  rfl

theorem actual_performance_difference_equals_advantage_return (M : Model S A)
    (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    expectedReturn M π' γ r - expectedReturn M π γ r =
      expectedReturn M π' γ (fun s _ =>
        averagedAdvantage M π' γ r (policyValue M π γ r) s) := by
  rw [actual_expected_performance_difference M π π' hw hw' γ hγ0 hγ1 r,
    actual_reward_return_identity M π' γ hγ0 hγ1]
  congr 1
  simp only [policyStateOccupancy, SafeLearning.CompleteFiniteCMDPFlow.stateMarginal,
    dotProduct, Finset.sum_mul]

theorem actual_performance_difference_literal_matrix_power_series (M : Model S A)
    (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    expectedReturn M π' γ r - expectedReturn M π γ r =
      ∑' n : ℕ, γ ^ n * ((M.initial ᵥ* (policyKernel M π') ^ n) ⬝ᵥ
        averagedAdvantage M π' γ r (policyValue M π γ r)) := by
  rw [actual_performance_difference_equals_advantage_return M π π' hw hw' γ hγ0 hγ1 r,
    actual_state_only_return_is_matrix_power_series M π' hw' γ]

end SafeLearning.CompleteFinitePolicyTrajectorySeries
