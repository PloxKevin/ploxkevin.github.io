import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SafeLearning.CompleteModulesLandscapeDelayFailure

def actualClockTrajectory (time : ℕ) : ℕ := time
def actualSafeBefore (delay : ℕ) : Set ℕ := {state | state<delay}
def actualViolationCost (delay time : ℕ) : ℝ := if delay≤ time then 1 else 0
def actualDiscountedTerm (gamma : ℝ) (delay time : ℕ) : ℝ := gamma^time*actualViolationCost delay time

theorem actual_time_counter_recurrence_and_source_violation_indicator (delay time : ℕ) :
    actualClockTrajectory (time+1)=actualClockTrajectory time+1 ∧
    actualViolationCost delay time=(actualSafeBefore delay)ᶜ.indicator
      (fun _ : ℕ=>(1:ℝ)) (actualClockTrajectory time) := by
  classical
  simp [actualClockTrajectory,actualSafeBefore,actualViolationCost,Set.indicator,not_lt]

theorem actual_arbitrary_delayed_violation_series_is_summable
    (gamma : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (delay : ℕ) :
    Summable (actualDiscountedTerm gamma delay) := by
  have geometric : Summable (fun time : ℕ=>gamma^time) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hgamma])
  apply Summable.of_nonneg_of_le (f:=fun time : ℕ=>gamma^time) _ _ geometric
  · intro time;dsimp [actualDiscountedTerm,actualViolationCost];split_ifs <;> positivity
  · intro time;by_cases h : delay≤ time <;> simp [actualDiscountedTerm,actualViolationCost,h] <;> positivity

theorem actual_full_delayed_discounted_cost_is_the_genuine_geometric_tail
    (gamma : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (delay : ℕ) :
    (∑' time : ℕ,actualDiscountedTerm gamma delay time)=gamma^delay/(1-gamma) := by
  have finitePart : ∑ time∈Finset.range delay,actualDiscountedTerm gamma delay time=0 := by
    apply Finset.sum_eq_zero
    intro time ht
    have h : ¬delay≤ time := by have := Finset.mem_range.mp ht;omega
    simp [actualDiscountedTerm,actualViolationCost,h]
  have tail : (fun time : ℕ=>actualDiscountedTerm gamma delay (time+delay))=
      (fun time : ℕ=>gamma^(time+delay)) := by
    funext time;simp [actualDiscountedTerm,actualViolationCost]
  have split := (actual_arbitrary_delayed_violation_series_is_summable gamma hgamma hgamma1 delay).sum_add_tsum_nat_add delay
  rw [finitePart,tail,zero_add] at split
  rw [←split]
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one (by rwa [abs_of_pos hgamma])]
  ring

theorem actual_exact_delay_budget_iff_the_literal_logarithmic_threshold
    (gamma budget : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1)
    (hbudget : 0<budget) (delay : ℕ) :
    (∑'time : ℕ,actualDiscountedTerm gamma delay time)≤ budget ↔
      Real.log (budget*(1-gamma))/Real.log gamma≤ (delay:ℝ) := by
  have hden : 0<1-gamma := sub_pos.mpr hgamma1
  have hlog : Real.log gamma<0 := Real.log_neg hgamma hgamma1
  rw [actual_full_delayed_discounted_cost_is_the_genuine_geometric_tail gamma hgamma hgamma1 delay,
    div_le_iff₀ hden,←Real.log_le_log_iff (pow_pos hgamma delay) (mul_pos hbudget hden),Real.log_pow,
    div_le_iff_of_neg hlog]

theorem actual_large_budget_accepts_every_delay_and_small_budget_logs_are_negative
    (gamma budget : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (hbudget : 0<budget) :
    ((1:ℝ)≤ budget*(1-gamma) → ∀ delay : ℕ,
      (∑'time : ℕ,actualDiscountedTerm gamma delay time)≤ budget) ∧
    (budget*(1-gamma)<1 → Real.log (budget*(1-gamma))<0 ∧ Real.log gamma<0) := by
  constructor
  · intro hb delay
    rw [actual_full_delayed_discounted_cost_is_the_genuine_geometric_tail gamma hgamma hgamma1 delay,
      div_le_iff₀ (sub_pos.mpr hgamma1)]
    exact (pow_le_one₀ hgamma.le hgamma1.le).trans hb
  · intro hb
    exact ⟨Real.log_neg (mul_pos hbudget (sub_pos.mpr hgamma1)) hb,Real.log_neg hgamma hgamma1⟩

theorem actual_every_positive_discounted_budget_accepts_a_certain_eventual_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (gamma budget : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (hbudget : 0<budget) :
    ∃ delay : ℕ,
      (∫ _ω : Ω,(∑'time : ℕ,actualDiscountedTerm gamma delay time) ∂P)≤ budget ∧
      P.real {_ω : Ω | ∃ time : ℕ,actualViolationCost delay time=1}=1 := by
  obtain ⟨delay,hdelay⟩ := exists_pow_lt_of_lt_one (mul_pos hbudget (sub_pos.mpr hgamma1)) hgamma1
  refine ⟨delay,?_,?_⟩
  · rw [integral_const]
    have hu : P.real Set.univ=1 := by simp
    rw [hu,one_smul]
    rw [actual_full_delayed_discounted_cost_is_the_genuine_geometric_tail gamma hgamma hgamma1 delay,
      div_le_iff₀ (sub_pos.mpr hgamma1)]
    exact hdelay.le
  · have event : {_ω : Ω | ∃ time : ℕ,actualViolationCost delay time=1}=(univ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      exact ⟨delay,by simp [actualViolationCost]⟩
    rw [event];simp

end SafeLearning.CompleteModulesLandscapeDelayFailure
