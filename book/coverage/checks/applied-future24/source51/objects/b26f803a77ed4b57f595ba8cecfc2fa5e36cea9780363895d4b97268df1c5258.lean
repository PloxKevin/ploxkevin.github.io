import SafeLearning.CompleteModulesPolicyDual

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesPolicyDualExample
open CompleteModulesPolicyDual

abbrev ActualMixedPolicy := {probability : ℝ // probability∈Icc (0:ℝ) 1}

def actualFirstActionPolicy : ActualMixedPolicy := ⟨1,by norm_num⟩
def actualSecondActionPolicy : ActualMixedPolicy := ⟨0,by norm_num⟩
instance : Nonempty ActualMixedPolicy := ⟨actualFirstActionPolicy⟩

def actualTwoActionReward : Fin 2→ℝ := ![1,0]
def actualTwoActionCost : Fin 2→ℝ := ![0,2]
def actualMixedWeights (policy : ActualMixedPolicy) : Fin 2→ℝ := ![policy.1,1-policy.1]
def actualMixedReward (policy : ActualMixedPolicy) : ℝ :=
  ∑ action,actualMixedWeights policy action*actualTwoActionReward action
def actualMixedCost (policy : ActualMixedPolicy) : ℝ :=
  ∑ action,actualMixedWeights policy action*actualTwoActionCost action

theorem actual_mixed_policy_is_a_normalized_nonnegative_two_action_law (policy : ActualMixedPolicy) :
    (∀ action,0  ≤  actualMixedWeights policy action) ∧ ∑ action,actualMixedWeights policy action=1 := by
  constructor
  · intro action;fin_cases action <;> simp [actualMixedWeights] <;> linarith [policy.2.1,policy.2.2]
  · simp [actualMixedWeights,Fin.sum_univ_two]

theorem actual_mixed_expected_reward_and_cost (policy : ActualMixedPolicy) :
    actualMixedReward policy=policy.1 ∧ actualMixedCost policy=2*(1-policy.1) := by
  simp [actualMixedReward,actualMixedCost,actualMixedWeights,actualTwoActionReward,
    actualTwoActionCost,Fin.sum_univ_two];ring

theorem actual_negative_price_strictly_lowers_lagrangian_at_every_strictly_feasible_policy
    {Policy : Type*} (reward cost : Policy→ℝ) (budget price : ℝ) (policy : Policy)
    (hfeasible : cost policy<budget) (hprice : price<0) :
    actualPolicyLagrangian reward cost budget price policy<reward policy := by
  have hp : 0 < price*(cost policy-budget) := mul_pos_of_neg_of_neg hprice (sub_neg.mpr hfeasible)
  unfold actualPolicyLagrangian;linarith

theorem actual_mixed_lagrangian_is_the_convex_combination_of_action_lagrangians
    (policy : ActualMixedPolicy) (price : ℝ) :
    actualPolicyLagrangian actualMixedReward actualMixedCost 1 price policy=
      policy.1*(1+price)+(1-policy.1)*(-price) := by
  rw [actualPolicyLagrangian,(actual_mixed_expected_reward_and_cost policy).1,
    (actual_mixed_expected_reward_and_cost policy).2];ring

theorem actual_mixing_cannot_exceed_the_better_action_lagrangian
    (policy : ActualMixedPolicy) (price : ℝ) :
    actualPolicyLagrangian actualMixedReward actualMixedCost 1 price policy ≤ max (1+price) (-price) := by
  rw [actual_mixed_lagrangian_is_the_convex_combination_of_action_lagrangians]
  have hf := mul_le_mul_of_nonneg_left (le_max_left (1+price) (-price)) policy.2.1
  have hs := mul_le_mul_of_nonneg_left (le_max_right (1+price) (-price)) (sub_nonneg.mpr policy.2.2)
  nlinarith only [hf,hs]

theorem actual_mixed_lagrangian_range_is_bounded (price : ℝ) :
    BddAbove (Set.range (actualPolicyLagrangian actualMixedReward actualMixedCost 1 price)) := by
  refine ⟨max (1+price) (-price),?_⟩
  rintro value ⟨policy,rfl⟩
  exact actual_mixing_cannot_exceed_the_better_action_lagrangian policy price

theorem actual_two_action_mixed_policy_dual_is_the_true_maximum (price : ℝ) :
    actualPolicyDual actualMixedReward actualMixedCost 1 price=max (1+price) (-price) := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro value ⟨policy,rfl⟩
    exact actual_mixing_cannot_exceed_the_better_action_lagrangian policy price
  · apply max_le
    · have h := le_csSup (actual_mixed_lagrangian_range_is_bounded price)
        (Set.mem_range_self actualFirstActionPolicy)
      simpa [actualPolicyDual,actual_mixed_lagrangian_is_the_convex_combination_of_action_lagrangians,
        actualFirstActionPolicy] using h
    · have h := le_csSup (actual_mixed_lagrangian_range_is_bounded price)
        (Set.mem_range_self actualSecondActionPolicy)
      simpa [actualPolicyDual,actual_mixed_lagrangian_is_the_convex_combination_of_action_lagrangians,
        actualSecondActionPolicy] using h

theorem actual_first_action_is_feasible_and_has_reward_one :
    actualMixedCost actualFirstActionPolicy ≤ 1 ∧ actualMixedReward actualFirstActionPolicy=1 := by
  rw [(actual_mixed_expected_reward_and_cost actualFirstActionPolicy).1,
    (actual_mixed_expected_reward_and_cost actualFirstActionPolicy).2]
  norm_num [actualFirstActionPolicy]

theorem actual_two_action_extended_primal_is_the_true_feasible_supremum_one :
    actualExtendedPolicyPrimal actualMixedReward actualMixedCost 1=1 := by
  apply le_antisymm
  · apply sSup_le
    rintro value ⟨policy,_,rfl⟩
    exact EReal.coe_le_coe ((actual_mixed_expected_reward_and_cost policy).1.le.trans policy.2.2)
  · apply le_sSup
    exact ⟨actualFirstActionPolicy,actual_first_action_is_feasible_and_has_reward_one.1,
      by rw [actual_first_action_is_feasible_and_has_reward_one.2];norm_num⟩

theorem actual_nonnegative_price_dual_minimum_is_one_at_zero :
    IsLeast (actualPolicyDual actualMixedReward actualMixedCost 1 '' Ici (0:ℝ)) 1 := by
  constructor
  · refine ⟨0,by simp,?_⟩
    norm_num [actual_two_action_mixed_policy_dual_is_the_true_maximum]
  · rintro value ⟨price,hprice,rfl⟩
    change 0 ≤ price at hprice
    rw [actual_two_action_mixed_policy_dual_is_the_true_maximum]
    exact (by linarith : (1:ℝ) ≤ 1+price).trans (le_max_left _ _)

theorem actual_unique_nonnegative_price_minimizer_is_zero (price : ℝ) (hprice : 0  ≤  price) :
    actualPolicyDual actualMixedReward actualMixedCost 1 price=1 ↔ price=0 := by
  rw [actual_two_action_mixed_policy_dual_is_the_true_maximum]
  constructor
  · intro he;have h := le_max_left (1+price) (-price);rw [he] at h;linarith
  · rintro rfl;norm_num

theorem actual_unrestricted_price_dual_minimum_is_one_half_at_negative_one_half :
    IsLeast (Set.range (actualPolicyDual actualMixedReward actualMixedCost 1)) (1/2) := by
  constructor
  · refine ⟨-1/2,?_⟩
    norm_num [actual_two_action_mixed_policy_dual_is_the_true_maximum]
  · rintro value ⟨price,rfl⟩
    rw [actual_two_action_mixed_policy_dual_is_the_true_maximum]
    have hf := le_max_left (1+price) (-price)
    have hs := le_max_right (1+price) (-price)
    linarith

theorem actual_unique_unrestricted_price_minimizer_is_negative_one_half (price : ℝ) :
    actualPolicyDual actualMixedReward actualMixedCost 1 price=1/2 ↔ price= -1/2 := by
  rw [actual_two_action_mixed_policy_dual_is_the_true_maximum]
  constructor
  · intro he
    have hf := le_max_left (1+price) (-price)
    have hs := le_max_right (1+price) (-price)
    rw [he] at hf hs;linarith
  · rintro rfl;norm_num

theorem actual_two_action_unrestricted_dual_undershoots_the_primal :
    (actualPolicyDual actualMixedReward actualMixedCost 1 (-1/2) : EReal)<
      actualExtendedPolicyPrimal actualMixedReward actualMixedCost 1 := by
  rw [(actual_unique_unrestricted_price_minimizer_is_negative_one_half (-1/2)).mpr rfl,
    actual_two_action_extended_primal_is_the_true_feasible_supremum_one]
  change ((1/2 : ℝ) : EReal)<((1 : ℝ) : EReal)
  exact EReal.coe_lt_coe_iff.mpr (by norm_num)

theorem actual_other_instance_has_dual_equal_to_the_unrestricted_price (price : ℝ) :
    actualPolicyDual (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 price=price := by
  unfold actualPolicyDual
  have he : actualPolicyLagrangian (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 price=
      (fun _ : Unit => price) := by funext policy;simp [actualPolicyLagrangian]
  rw [he];simp

theorem actual_unrestricted_dual_need_not_be_bounded_below :
    ¬BddBelow (Set.range (actualPolicyDual (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1)) := by
  rintro ⟨bound,hbound⟩
  have h := hbound (Set.mem_range_self (bound-1))
  rw [actual_other_instance_has_dual_equal_to_the_unrestricted_price] at h
  linarith

end SafeLearning.CompleteModulesPolicyDualExample
