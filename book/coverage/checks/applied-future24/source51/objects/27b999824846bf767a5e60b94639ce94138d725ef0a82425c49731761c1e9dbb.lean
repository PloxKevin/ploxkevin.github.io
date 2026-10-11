import SafeLearning.CompleteFiniteCMDPInverse

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFinitePolicyValues

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery SafeLearning.CompleteFiniteCMDPInverse

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

def policyKernel (M : Model S A) (π : Policy S A) : Matrix S S ℝ :=
  stationaryKernel M (π.action 0)

def policyReward (π : Policy S A) (r : S → A → ℝ) (s : S) : ℝ :=
  ∑ a, π.action 0 s a * r s a

def policyValue (M : Model S A) (π : Policy S A) (γ : ℝ) (r : S → A → ℝ) : S → ℝ :=
  (discountedMatrix (policyKernel M π) γ)⁻¹ *ᵥ policyReward π r

def actionValue (M : Model S A) (γ : ℝ) (r : S → A → ℝ) (v : S → ℝ)
    (s : S) (a : A) : ℝ := r s a + γ * ∑ t, M.transition s a t * v t

def actionAdvantage (M : Model S A) (γ : ℝ) (r : S → A → ℝ) (v : S → ℝ)
    (s : S) (a : A) : ℝ := actionValue M γ r v s a - v s

def averagedAdvantage (M : Model S A) (π : Policy S A) (γ : ℝ)
    (r : S → A → ℝ) (v : S → ℝ) (s : S) : ℝ :=
  ∑ a, π.action 0 s a * actionAdvantage M γ r v s a

theorem actual_policy_kernel_probability_law (M : Model S A) (π : Policy S A) :
    (∀ s t, 0 ≤ policyKernel M π s t) ∧ ∀ s, ∑ t, policyKernel M π s t = 1 :=
  actual_stationary_kernel_probability_law M (π.action 0)
    (π.action_nonneg 0) (π.action_sum 0)

theorem actual_inverse_value_satisfies_bellman (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) (s : S) :
    policyValue M π γ r s = policyReward π r s +
      γ * (policyKernel M π *ᵥ policyValue M π γ r) s := by
  have hK := actual_policy_kernel_probability_law M π
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse
    (policyKernel M π) hK.1 hK.2 γ hγ0 hγ1).1
  have he : discountedMatrix (policyKernel M π) γ *ᵥ policyValue M π γ r =
      policyReward π r := by
    rw [policyValue, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  have hs := congrArg (fun v : S → ℝ => v s) he
  simp only [discountedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs
  linarith

theorem actual_bellman_solution_is_inverse_value (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) (v : S → ℝ)
    (hv : ∀ s, v s = policyReward π r s + γ * (policyKernel M π *ᵥ v) s) :
    v = policyValue M π γ r := by
  have hK := actual_policy_kernel_probability_law M π
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse
    (policyKernel M π) hK.1 hK.2 γ hγ0 hγ1).2
  have he : discountedMatrix (policyKernel M π) γ *ᵥ v = policyReward π r := by
    ext s
    simp only [discountedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hv s]
  calc
    v = ((discountedMatrix (policyKernel M π) γ)⁻¹ *
        discountedMatrix (policyKernel M π) γ) *ᵥ v := by rw [hi, Matrix.one_mulVec]
    _ = policyValue M π γ r := by rw [← Matrix.mulVec_mulVec, he]; rfl

theorem actual_averaged_advantage_formula (M : Model S A) (π : Policy S A)
    (γ : ℝ) (r : S → A → ℝ) (v : S → ℝ) (s : S) :
    averagedAdvantage M π γ r v s = policyReward π r s +
      γ * (policyKernel M π *ᵥ v) s - v s := by
  have hconst : (∑ a, π.action 0 s a * v s) = v s := by
    rw [← Finset.sum_mul, π.action_sum, one_mul]
  have htransition : (∑ a, π.action 0 s a * (∑ t, M.transition s a t * v t)) =
      (policyKernel M π *ᵥ v) s := by
    simp only [policyKernel, stationaryKernel, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  simp only [averagedAdvantage, actionAdvantage, actionValue, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, policyReward]
  rw [hconst]
  have hscaled : (∑ a, π.action 0 s a * (γ * ∑ t, M.transition s a t * v t)) =
      γ * (policyKernel M π *ᵥ v) s := by
    rw [← htransition, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hscaled]

theorem actual_value_difference_literal_inverse (M : Model S A) (π π' : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    policyValue M π' γ r - policyValue M π γ r =
      (discountedMatrix (policyKernel M π') γ)⁻¹ *ᵥ
        averagedAdvantage M π' γ r (policyValue M π γ r) := by
  have hK := actual_policy_kernel_probability_law M π'
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse
    (policyKernel M π') hK.1 hK.2 γ hγ0 hγ1).2
  have he : discountedMatrix (policyKernel M π') γ *ᵥ
      (policyValue M π' γ r - policyValue M π γ r) =
        averagedAdvantage M π' γ r (policyValue M π γ r) := by
    ext s
    rw [actual_averaged_advantage_formula]
    simp only [discountedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.mulVec_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [actual_inverse_value_satisfies_bellman M π' γ hγ0 hγ1 r s]
  calc
    _ = ((discountedMatrix (policyKernel M π') γ)⁻¹ *
        discountedMatrix (policyKernel M π') γ) *ᵥ
          (policyValue M π' γ r - policyValue M π γ r) := by rw [hi, Matrix.one_mulVec]
    _ = _ := by rw [← Matrix.mulVec_mulVec, he]

end SafeLearning.CompleteFinitePolicyValues
