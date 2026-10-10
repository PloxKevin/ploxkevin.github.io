import SafeLearning.CompleteFinitePolicyValues
import SafeLearning.CompleteFiniteMarkovPathCorrespondence

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open MeasureTheory

namespace SafeLearning.CompleteFinitePolicyPerformance

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery SafeLearning.CompleteFiniteCMDPInverse
  SafeLearning.CompleteFinitePolicyValues SafeLearning.CompleteFiniteControlledPathMeasure
  SafeLearning.CompleteFiniteMarkovPathCorrespondence

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

def policyStateOccupancy (M : Model S A) (π : Policy S A) (γ : ℝ) : S → ℝ :=
  stateMarginal (occupancy M π γ)

theorem actual_stationary_state_occupancy_fixed_point (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (t : S) :
    policyStateOccupancy M π γ t = (1 - γ) * M.initial t +
      γ * ∑ s, policyStateOccupancy M π γ s * policyKernel M π s t := by
  exact actual_flow_factorization_gives_kernel_fixed_point M γ (occupancy M π γ)
    (π.action 0) (actual_occupancy_satisfies_flow M π γ hγ0 hγ1)
    (fun s a => (actual_stationary_occupancy_factorization M π hw γ hγ0 hγ1 s a).symm) t

theorem actual_stationary_state_occupancy_resolvent_equation (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    policyStateOccupancy M π γ ᵥ* discountedMatrix (policyKernel M π) γ =
      (1 - γ) • M.initial := by
  ext t
  simp only [discountedMatrix, Matrix.vecMul_sub, Matrix.vecMul_one,
    Matrix.vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change policyStateOccupancy M π γ t -
    γ * (∑ s, policyStateOccupancy M π γ s * policyKernel M π s t) =
      (1 - γ) * M.initial t
  linarith [actual_stationary_state_occupancy_fixed_point M π hw γ hγ0 hγ1 t]

theorem actual_weighted_discounted_bellman_identity (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v : S → ℝ) :
    policyStateOccupancy M π γ ⬝ᵥ (discountedMatrix (policyKernel M π) γ *ᵥ v) =
      (1 - γ) * (M.initial ⬝ᵥ v) := by
  rw [Matrix.dotProduct_mulVec,
    actual_stationary_state_occupancy_resolvent_equation M π hw γ hγ0 hγ1,
    smul_dotProduct, smul_eq_mul]

theorem actual_expected_return_equals_initial_value (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    expectedReturn M π γ r = M.initial ⬝ᵥ policyValue M π γ r := by
  have hreward : (∑ s, ∑ a, occupancy M π γ s a * r s a) =
      policyStateOccupancy M π γ ⬝ᵥ policyReward π r := by
    simp only [dotProduct, policyReward]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [actual_stationary_occupancy_factorization M π hw γ hγ0 hγ1 s a]
    change stateMarginal (occupancy M π γ) s * π.action 0 s a * r s a =
      stateMarginal (occupancy M π γ) s * (π.action 0 s a * r s a)
    ring
  have hK := actual_policy_kernel_probability_law M π
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse
    (policyKernel M π) hK.1 hK.2 γ hγ0 hγ1).1
  have hbell : policyReward π r =
      discountedMatrix (policyKernel M π) γ *ᵥ policyValue M π γ r := by
    rw [policyValue, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  rw [actual_reward_return_identity M π γ hγ0 hγ1 r, hreward, hbell,
    actual_weighted_discounted_bellman_identity M π hw γ hγ0 hγ1]
  exact mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hγ1))

theorem actual_expected_performance_difference (M : Model S A) (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    expectedReturn M π' γ r - expectedReturn M π γ r =
      (policyStateOccupancy M π' γ ⬝ᵥ
        averagedAdvantage M π' γ r (policyValue M π γ r)) / (1 - γ) := by
  have hK := actual_policy_kernel_probability_law M π'
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse
    (policyKernel M π') hK.1 hK.2 γ hγ0 hγ1).1
  have h := actual_weighted_discounted_bellman_identity M π' hw' γ hγ0 hγ1
    (policyValue M π' γ r - policyValue M π γ r)
  nth_rw 1 [actual_value_difference_literal_inverse M π π' γ hγ0 hγ1 r] at h
  rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] at h
  rw [actual_expected_return_equals_initial_value M π' hw' γ hγ0 hγ1 r,
    actual_expected_return_equals_initial_value M π hw γ hγ0 hγ1 r]
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr hγ1))).2
  rw [dotProduct_sub] at h
  nlinarith [h]

section Paths

variable [MeasurableSpace S] [MeasurableSpace A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass A]

theorem actual_constructed_path_return_equals_initial_value (M : Model S A) (π : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2
      ∂controlledPathMeasure M (markovHistoryPolicy π)) =
        M.initial ⬝ᵥ policyValue M π γ r := by
  rw [actual_constructed_markov_path_expected_return M π γ hγ0 hγ1 r,
    actual_expected_return_equals_initial_value M π hw γ hγ0 hγ1 r]

theorem actual_constructed_path_performance_difference (M : Model S A) (π π' : Policy S A)
    (hw : ∀ n s a, π.action n s a = π.action 0 s a)
    (hw' : ∀ n s a, π'.action n s a = π'.action 0 s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2
      ∂controlledPathMeasure M (markovHistoryPolicy π')) -
    (∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2
      ∂controlledPathMeasure M (markovHistoryPolicy π)) =
        (policyStateOccupancy M π' γ ⬝ᵥ
          averagedAdvantage M π' γ r (policyValue M π γ r)) / (1 - γ) := by
  rw [actual_constructed_markov_path_expected_return M π' γ hγ0 hγ1 r,
    actual_constructed_markov_path_expected_return M π γ hγ0 hγ1 r]
  exact actual_expected_performance_difference M π π' hw hw' γ hγ0 hγ1 r

end Paths

end SafeLearning.CompleteFinitePolicyPerformance
