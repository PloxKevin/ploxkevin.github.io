import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace SafeLearning.CompleteAppliedClippingGAE

def actualClip (ratio : ℝ) : ℝ := max (4/5) (min (6/5) ratio)
def actualClippedReward (advantage ratio : ℝ) : ℝ :=
  min (ratio*advantage) (actualClip ratio*advantage)
def actualPessimisticCost (advantage ratio : ℝ) : ℝ :=
  max (ratio*advantage) (actualClip ratio*advantage)

theorem actual_reward_clipping_is_below_the_raw_term_and_cost_is_above_it
    (advantage ratio : ℝ) :
    actualClippedReward advantage ratio≤ratio*advantage ∧
      ratio*advantage≤actualPessimisticCost advantage ratio :=
  ⟨min_le_left _ _,le_max_left _ _⟩

theorem actual_positive_advantage_clips_only_the_upper_ratio
    (advantage ratio : ℝ) (ha : 0≤advantage) :
    actualClippedReward advantage ratio=min ratio (6/5)*advantage := by
  unfold actualClippedReward actualClip
  simp only [min_def,max_def]
  split_ifs <;> nlinarith

theorem actual_negative_advantage_clips_only_the_lower_ratio
    (advantage ratio : ℝ) (ha : advantage≤0) :
    actualClippedReward advantage ratio=max ratio (4/5)*advantage := by
  unfold actualClippedReward actualClip
  simp only [min_def,max_def]
  split_ifs <;> nlinarith

theorem actual_positive_advantage_upper_branch_has_zero_derivative
    (advantage ratio : ℝ) (ha : 0≤advantage) (hr : 6/5<ratio) :
    HasDerivAt (actualClippedReward advantage) 0 ratio := by
  apply (hasDerivAt_const ratio ((6/5)*advantage)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with value hv
  rw [actual_positive_advantage_clips_only_the_upper_ratio advantage value ha,
    min_eq_right hv.le]

theorem actual_positive_advantage_lower_branch_has_derivative_advantage
    (advantage ratio : ℝ) (ha : 0≤advantage) (hr : ratio<6/5) :
    HasDerivAt (actualClippedReward advantage) advantage ratio := by
  have hd : HasDerivAt (fun value : ℝ=>value*advantage) advantage ratio := by
    simpa using (hasDerivAt_id ratio).mul_const advantage
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hr] with value hv
  rw [actual_positive_advantage_clips_only_the_upper_ratio advantage value ha,
    min_eq_left hv.le]

theorem actual_negative_advantage_lower_branch_has_zero_derivative
    (advantage ratio : ℝ) (ha : advantage≤0) (hr : ratio<4/5) :
    HasDerivAt (actualClippedReward advantage) 0 ratio := by
  apply (hasDerivAt_const ratio ((4/5)*advantage)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hr] with value hv
  rw [actual_negative_advantage_clips_only_the_lower_ratio advantage value ha,
    max_eq_right hv.le]

theorem actual_negative_advantage_upper_branch_has_derivative_advantage
    (advantage ratio : ℝ) (ha : advantage≤0) (hr : 4/5<ratio) :
    HasDerivAt (actualClippedReward advantage) advantage ratio := by
  have hd : HasDerivAt (fun value : ℝ=>value*advantage) advantage ratio := by
    simpa using (hasDerivAt_id ratio).mul_const advantage
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with value hv
  rw [actual_negative_advantage_clips_only_the_lower_ratio advantage value ha,
    max_eq_left hv.le]

theorem actual_source_four_reward_cases_two_cost_cases_and_derivatives :
    actualClippedReward 1 (13/10)=6/5 ∧
    actualClippedReward 1 (7/10)=7/10 ∧
    actualClippedReward (-1) (7/10)=-(4/5) ∧
    actualClippedReward (-1) (13/10)=-(13/10) ∧
    actualPessimisticCost 1 (7/10)=4/5 ∧
    actualPessimisticCost (-1) (13/10)=-(6/5) ∧
    HasDerivAt (actualClippedReward 1) 0 (13/10) ∧
    HasDerivAt (actualClippedReward 1) 1 (7/10) ∧
    HasDerivAt (actualClippedReward (-1)) 0 (7/10) ∧
    HasDerivAt (actualClippedReward (-1)) (-1) (13/10) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · norm_num [actualClippedReward,actualPessimisticCost,actualClip]
  · exact actual_positive_advantage_upper_branch_has_zero_derivative _ _ (by norm_num) (by norm_num)
  · exact actual_positive_advantage_lower_branch_has_derivative_advantage _ _ (by norm_num) (by norm_num)
  · exact actual_negative_advantage_lower_branch_has_zero_derivative _ _ (by norm_num) (by norm_num)
  · exact actual_negative_advantage_upper_branch_has_derivative_advantage _ _ (by norm_num) (by norm_num)

def actualTD (reward value : ℕ→ℝ) (discount : ℝ) (time : ℕ) : ℝ :=
  reward time+discount*value (time+1)-value time

def actualGAE (delta : ℕ→ℝ) (decay : ℝ) : ℕ→ℕ→ℝ
  | 0,_ => 0
  | remaining+1,time => delta time+decay*actualGAE delta decay remaining (time+1)

theorem actual_gae_is_the_full_finite_discounted_td_sum
    (delta : ℕ→ℝ) (decay : ℝ) (remaining time : ℕ) :
    actualGAE delta decay remaining time=
      ∑ offset∈Finset.range remaining,decay^offset*delta (time+offset) := by
  induction remaining generalizing time with
  | zero => simp [actualGAE]
  | succ remaining ih =>
    rw [actualGAE,ih,Finset.sum_range_succ']
    simp only [pow_zero,one_mul,Nat.add_zero]
    rw [add_comm (∑ k∈Finset.range remaining,decay^(k+1)*delta (time+(k+1))) (delta time)]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro offset ho
    rw [pow_succ]
    have he : time+1+offset=time+(offset+1) := by omega
    rw [he]
    ring

theorem actual_lambda_one_gae_is_the_true_return_minus_value_with_terminal_value
    (reward value : ℕ→ℝ) (discount : ℝ) (remaining time : ℕ) :
    actualGAE (actualTD reward value discount) discount remaining time=
      (∑ offset∈Finset.range remaining,discount^offset*reward (time+offset))+
        discount^remaining*value (time+remaining)-value time := by
  induction remaining generalizing time with
  | zero => simp [actualGAE]
  | succ remaining ih =>
    rw [actualGAE,ih,Finset.sum_range_succ']
    simp only [actualTD,pow_zero,one_mul,Nat.add_zero]
    have hs : (∑ offset∈Finset.range remaining,discount^(offset+1)*reward (time+(offset+1)))=
        discount*(∑ offset∈Finset.range remaining,discount^offset*reward (time+1+offset)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro offset ho
      rw [pow_succ]
      have he : time+(offset+1)=time+1+offset := by omega
      rw [he];ring
    rw [hs,pow_succ]
    have he : time+(remaining+1)=time+1+remaining := by omega
    rw [he]
    ring

def sourceReward : ℕ→ℝ := fun time=>if time=2 then 1 else 0
def sourceValue : ℕ→ℝ := fun time=>if time=0 then 1/2 else
  if time=1 then 3/5 else if time=2 then 4/5 else 0

theorem actual_source_td_and_all_three_gae_advantages_and_lambda_return :
    actualTD sourceReward sourceValue (9/10) 0=1/25 ∧
    actualTD sourceReward sourceValue (9/10) 1=3/25 ∧
    actualTD sourceReward sourceValue (9/10) 2=1/5 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) ((9/10)*(1/2)) 1 2=1/5 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) ((9/10)*(1/2)) 2 1=21/100 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) ((9/10)*(1/2)) 3 0=269/2000 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) (9/10) 3 0=31/100 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) (9/10) 3 0=(9/10)^2*1-sourceValue 0 ∧
    actualGAE (actualTD sourceReward sourceValue (9/10)) ((9/10)*(1/2)) 3 0+sourceValue 0=1269/2000 := by
  norm_num [actualTD,actualGAE,sourceReward,sourceValue]

end SafeLearning.CompleteAppliedClippingGAE
