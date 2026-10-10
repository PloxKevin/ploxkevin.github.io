import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesPolicyDual

variable {Policy : Type*} [Nonempty Policy]

def actualPolicyLagrangian (reward cost : Policy → ℝ) (budget price : ℝ) (policy : Policy) : ℝ :=
  reward policy-price*(cost policy-budget)

def actualPolicyDual (reward cost : Policy → ℝ) (budget price : ℝ) : ℝ :=
  sSup (Set.range (actualPolicyLagrangian reward cost budget price))

def actualExtendedPolicyPrimal (reward cost : Policy → ℝ) (budget : ℝ) : EReal :=
  sSup {value | ∃ policy,cost policy≤budget ∧ value=(reward policy : EReal)}

omit [Nonempty Policy] in
theorem actual_bounded_returns_bound_each_lagrangian
    (reward cost : Policy → ℝ) (budget price rewardBound costBound : ℝ)
    (hreward : ∀ policy,|reward policy|≤rewardBound)
    (hcost : ∀ policy,|cost policy|≤costBound) (policy : Policy) :
    |actualPolicyLagrangian reward cost budget price policy|≤
      rewardBound+|price| * (costBound+|budget|) := by
  unfold actualPolicyLagrangian
  calc
    _ ≤ |reward policy|+|price*(cost policy-budget)| := abs_sub _ _
    _ = |reward policy|+|price| * |cost policy-budget| := by rw [abs_mul]
    _ ≤ rewardBound+|price| * (costBound+|budget|) :=
      add_le_add (hreward policy) (mul_le_mul_of_nonneg_left
        ((abs_sub (cost policy) budget).trans (add_le_add (hcost policy) le_rfl)) (abs_nonneg price))

omit [Nonempty Policy] in
theorem actual_policy_lagrangian_range_is_bounded_above
    (reward cost : Policy → ℝ) (budget price rewardBound costBound : ℝ)
    (hreward : ∀ policy,|reward policy|≤rewardBound)
    (hcost : ∀ policy,|cost policy|≤costBound) :
    BddAbove (Set.range (actualPolicyLagrangian reward cost budget price)) := by
  refine ⟨rewardBound+|price| * (costBound+|budget|),?_⟩
  rintro value ⟨policy,rfl⟩
  exact (le_abs_self _).trans
    (actual_bounded_returns_bound_each_lagrangian reward cost budget price rewardBound costBound hreward hcost policy)

omit [Nonempty Policy] in
theorem actual_policy_lagrangian_is_affine_in_price
    (reward cost : Policy → ℝ) (budget firstPrice secondPrice left right : ℝ)
    (hsum : left+right=1) (policy : Policy) :
    actualPolicyLagrangian reward cost budget (left*firstPrice+right*secondPrice) policy=
      left*actualPolicyLagrangian reward cost budget firstPrice policy+
        right*actualPolicyLagrangian reward cost budget secondPrice policy := by
  unfold actualPolicyLagrangian
  linear_combination -(reward policy) * hsum

theorem actual_policy_dual_is_convex_for_arbitrary_nonconvex_policy_class
    (reward cost : Policy → ℝ) (budget rewardBound costBound : ℝ)
    (hreward : ∀ policy,|reward policy|≤rewardBound)
    (hcost : ∀ policy,|cost policy|≤costBound) :
    ConvexOn ℝ Set.univ (actualPolicyDual reward cost budget) := by
  constructor
  · exact convex_univ
  · intro firstPrice _ secondPrice _ left right hleft hright hsum
    change actualPolicyDual reward cost budget (left*firstPrice+right*secondPrice)≤
      left*actualPolicyDual reward cost budget firstPrice+right*actualPolicyDual reward cost budget secondPrice
    unfold actualPolicyDual
    apply csSup_le (Set.range_nonempty _)
    rintro value ⟨policy,rfl⟩
    rw [actual_policy_lagrangian_is_affine_in_price reward cost budget firstPrice secondPrice left right hsum]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (le_csSup (actual_policy_lagrangian_range_is_bounded_above reward cost budget firstPrice
          rewardBound costBound hreward hcost) (Set.mem_range_self policy)) hleft
    · exact mul_le_mul_of_nonneg_left
        (le_csSup (actual_policy_lagrangian_range_is_bounded_above reward cost budget secondPrice
          rewardBound costBound hreward hcost) (Set.mem_range_self policy)) hright

omit [Nonempty Policy] in
theorem actual_feasible_reward_is_bounded_by_each_nonnegative_price_dual
    (reward cost : Policy → ℝ) (budget price rewardBound costBound : ℝ)
    (hreward : ∀ policy,|reward policy|≤rewardBound)
    (hcost : ∀ policy,|cost policy|≤costBound)
    (policy : Policy) (hfeasible : cost policy≤budget) (hprice : 0≤price) :
    reward policy≤actualPolicyDual reward cost budget price := by
  have hp : price*(cost policy-budget)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos hprice (sub_nonpos.mpr hfeasible)
  have h : actualPolicyLagrangian reward cost budget price policy≤
      actualPolicyDual reward cost budget price :=
    le_csSup (actual_policy_lagrangian_range_is_bounded_above reward cost budget price
      rewardBound costBound hreward hcost) (Set.mem_range_self policy)
  unfold actualPolicyLagrangian at h
  linarith

omit [Nonempty Policy] in
theorem actual_true_extended_supremum_primal_is_bounded_by_each_dual
    (reward cost : Policy → ℝ) (budget price rewardBound costBound : ℝ)
    (hreward : ∀ policy,|reward policy|≤rewardBound)
    (hcost : ∀ policy,|cost policy|≤costBound) (hprice : 0≤price) :
    actualExtendedPolicyPrimal reward cost budget≤(actualPolicyDual reward cost budget price : EReal) := by
  apply sSup_le
  rintro value ⟨policy,hfeasible,rfl⟩
  exact EReal.coe_le_coe
    (actual_feasible_reward_is_bounded_by_each_nonnegative_price_dual reward cost budget price
      rewardBound costBound hreward hcost policy hfeasible hprice)

omit [Nonempty Policy] in
theorem actual_empty_feasible_class_has_minus_infinity_primal
    (reward cost : Policy → ℝ) (budget : ℝ) (hinfeasible : ∀ policy,budget<cost policy) :
    actualExtendedPolicyPrimal reward cost budget=⊥ := by
  unfold actualExtendedPolicyPrimal
  have he : {value : EReal | ∃ policy,cost policy≤budget ∧ value=(reward policy : EReal)}=∅ := by
    ext value
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨policy,hfeasible,_⟩
    exact (not_le_of_gt (hinfeasible policy)) hfeasible
  rw [he,sSup_empty]

theorem actual_negative_price_counterexample :
    actualExtendedPolicyPrimal (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1=0 ∧
    actualPolicyDual (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 (-1)= -1 ∧
    ¬(actualExtendedPolicyPrimal (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1≤
      (actualPolicyDual (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 (-1) : EReal)) := by
  have hp : actualExtendedPolicyPrimal (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1=0 := by
    unfold actualExtendedPolicyPrimal
    have he : {value : EReal | ∃ policy : Unit,(0:ℝ)≤1 ∧ value=((0:ℝ) : EReal)}={0} := by
      ext value;simp
    rw [he,sSup_singleton]
  have hd : actualPolicyDual (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 (-1)= -1 := by
    unfold actualPolicyDual
    have he : actualPolicyLagrangian (fun _ : Unit => (0:ℝ)) (fun _ : Unit => (0:ℝ)) 1 (-1)=
        (fun _ : Unit => (-1:ℝ)) := by
      funext policy
      norm_num [actualPolicyLagrangian]
    rw [he]
    simp
  refine ⟨hp,hd,?_⟩
  rw [hp,hd]
  norm_num

end SafeLearning.CompleteModulesPolicyDual
