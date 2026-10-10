import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SafeLearning.CompleteModulesLandscapeDiscountedFailure

def sourceViolationCost (t : ℕ) : ℝ := if 50≤t then 1 else 0
def sourceDiscountedTerm (t : ℕ) : ℝ := (9/10:ℝ)^t*sourceViolationCost t
def sourceUndiscountedCount (t : ℕ) : ℝ≥0∞ := if 50≤t then 1 else 0

theorem actual_source_indicator_is_zero_before_fifty_and_one_afterwards (t : ℕ) :
    (sourceViolationCost t=0 ↔ t<50) ∧ (sourceViolationCost t=1 ↔ 50≤t) := by
  by_cases h : 50≤t <;> simp [sourceViolationCost,h] <;> omega

theorem actual_discounted_indicator_cost_is_summable : Summable sourceDiscountedTerm := by
  have geometric : Summable (fun t : ℕ => (9/10:ℝ)^t) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  apply Summable.of_nonneg_of_le (f:=fun t : ℕ => (9/10:ℝ)^t) _ _ geometric
  · intro t;dsimp [sourceDiscountedTerm,sourceViolationCost];split_ifs <;> positivity
  · intro t;by_cases h : 50≤t <;> simp [sourceDiscountedTerm,sourceViolationCost,h] <;> positivity

theorem actual_full_source_discounted_cost_equals_the_shifted_geometric_tail :
    (∑' t : ℕ,sourceDiscountedTerm t)=∑' t : ℕ,(9/10:ℝ)^(t+50) := by
  have finitePart : ∑ t∈Finset.range 50,sourceDiscountedTerm t=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have h : ¬50≤t := by have := Finset.mem_range.mp ht;omega
    simp [sourceDiscountedTerm,sourceViolationCost,h]
  have tail : (fun t : ℕ => sourceDiscountedTerm (t+50))=(fun t : ℕ =>(9/10:ℝ)^(t+50)) := by
    funext t;simp [sourceDiscountedTerm,sourceViolationCost]
  have split := actual_discounted_indicator_cost_is_summable.sum_add_tsum_nat_add 50
  rw [finitePart,tail,zero_add] at split
  exact split.symm

theorem actual_source_discounted_sum_exact_value_rounding_and_budget_pass :
    (∑'t : ℕ,sourceDiscountedTerm t)=(9/10:ℝ)^50/(1-9/10) ∧
    |(∑'t : ℕ,sourceDiscountedTerm t)-(0.0515378:ℝ)|≤0.00000005 ∧
    (∑'t : ℕ,sourceDiscountedTerm t)≤(0.1:ℝ) := by
  have exact_value : (∑'t : ℕ,sourceDiscountedTerm t)=(9/10:ℝ)^50/(1-9/10) := by
    rw [actual_full_source_discounted_cost_equals_the_shifted_geometric_tail]
    simp_rw [pow_add]
    rw [tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(9/10:ℝ)|<1)]
    ring
  refine ⟨exact_value,?_,?_⟩
  all_goals rw [exact_value];norm_num

theorem actual_source_deterministic_eventual_failure_probability_is_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    P.real { _ω : Ω | ∃ t : ℕ,sourceViolationCost t=1}=1 := by
  have event : { _ω : Ω | ∃ t : ℕ,sourceViolationCost t=1}=(univ : Set Ω) := by
    ext ω;simp only [mem_setOf_eq,mem_univ,iff_true]
    exact ⟨50,by norm_num [sourceViolationCost]⟩
  rw [event];simp

theorem actual_undiscounted_total_unsafe_step_count_is_infinite :
    (∑'t : ℕ,sourceUndiscountedCount t)=∞ := by
  have injection : Function.Injective (fun t : ℕ => t+50) := fun _ _ h => Nat.add_right_cancel h
  have lower := ENNReal.tsum_comp_le_tsum_of_injective injection sourceUndiscountedCount
  have tail : (∑'t : ℕ,sourceUndiscountedCount (t+50))=∞ := by
    simp only [sourceUndiscountedCount,Nat.le_add_left,ite_true]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
  rw [tail] at lower
  exact top_unique lower

theorem actual_any_infinite_horizon_failure_budget_below_one_fails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure_budget : ℝ) (hbudget : failure_budget<1) :
    ¬P.real {_ω : Ω | ∃t : ℕ,sourceViolationCost t=1}≤failure_budget := by
  rw [actual_source_deterministic_eventual_failure_probability_is_one]
  exact not_le.mpr hbudget

end SafeLearning.CompleteModulesLandscapeDiscountedFailure
