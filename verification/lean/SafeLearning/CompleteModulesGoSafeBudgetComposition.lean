import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace SafeLearning.CompleteModulesGoSafeBudgetComposition

theorem actual_nonnegative_integrable_infinite_cost_has_the_literal_suffix_identity
    (cost : ℝ→ℝ) (time budget : ℝ) (htime : 0 ≤ time)
    (hint : IntegrableOn cost (Ici 0)) (hnonnegative : ∀ t,0 ≤ t → 0 ≤ cost t)
    (hbudget : (∫ t in Ici (0:ℝ),cost t) ≤ budget) :
    (∫ t in Ici time,cost t)=(∫ t in Ici (0:ℝ),cost t)-(∫ t in (0:ℝ)..time,cost t) ∧
      (∫ t in Ici time,cost t) ≤ (∫ t in Ici (0:ℝ),cost t) ∧
      (∫ t in Ici time,cost t) ≤ budget := by
  have htail : IntegrableOn cost (Ici time) := hint.mono_set (Ici_subset_Ici.mpr htime)
  have he := intervalIntegral.integral_Ici_sub_Ici' hint htail
  have hn : 0 ≤ ∫ t in (0:ℝ)..time,cost t :=
    intervalIntegral.integral_nonneg htime (fun t ht=>hnonnegative t ht.1)
  refine ⟨by linarith,by linarith,by linarith⟩

/-- A fixed state cost and an autonomous clock backup. The untested controller
holds the same initial state for one time unit before switching to the backup. -/
def actualStateCost : ℝ→ℝ := (Icc (1:ℝ) 2).indicator (fun _=>3/4)
def actualClockBackupPath (time initial : ℝ) : ℝ := initial+time
def actualHeldThenClockPath (time : ℝ) : ℝ := max 1 time

theorem actual_clock_backup_and_held_prefix_have_their_genuine_dynamics
    (initial time : ℝ) :
    actualClockBackupPath 0 initial=initial ∧
      HasDerivAt (fun t=>actualClockBackupPath t initial) 1 time ∧
      HasDerivAt (fun _t : ℝ=>initial) 0 time := by
  exact ⟨by simp [actualClockBackupPath],(hasDerivAt_id time).const_add initial,hasDerivAt_const time initial⟩

theorem actual_stitched_path_is_continuous_and_switches_from_hold_to_the_same_backup :
    Continuous actualHeldThenClockPath ∧ actualHeldThenClockPath 0=1 ∧
      (∀ time∈Icc (0:ℝ) 1,actualHeldThenClockPath time=1) ∧
      (∀ time : ℝ,1 ≤ time → actualHeldThenClockPath time=actualClockBackupPath (time-1) 1) := by
  refine ⟨by unfold actualHeldThenClockPath;fun_prop,by norm_num [actualHeldThenClockPath],?_,?_⟩
  · intro time ht
    exact max_eq_left ht.2
  · intro time ht
    rw [actualHeldThenClockPath,max_eq_right ht]
    unfold actualClockBackupPath
    ring

theorem actual_fixed_state_cost_is_nonnegative (state : ℝ) : 0 ≤ actualStateCost state := by
  unfold actualStateCost
  by_cases h : state∈Icc (1:ℝ) 2 <;> norm_num [h]

theorem actual_clock_backup_cost_is_an_actual_unit_interval_indicator :
    (fun t : ℝ=>actualStateCost (actualClockBackupPath t 1))=
      (Icc (0:ℝ) 1).indicator (fun _=>3/4) := by
  ext t
  by_cases h : t∈Icc (0:ℝ) 1
  · have hs : 1+t∈Icc (1:ℝ) 2 := ⟨by linarith [h.1],by linarith [h.2]⟩
    simp [actualStateCost,actualClockBackupPath,h,hs]
  · have hs : 1+t∉Icc (1:ℝ) 2 := by
      intro hs
      apply h
      constructor <;> linarith [hs.1,hs.2]
    simp [actualStateCost,actualClockBackupPath,h,hs]

theorem actual_stitched_state_cost_on_future_times_is_the_double_interval_indicator
    (time : ℝ) (htime : 0 ≤ time) :
    actualStateCost (actualHeldThenClockPath time)=
      (Icc (0:ℝ) 2).indicator (fun _=>3/4) time := by
  by_cases h : time ≤ 2
  · have hs : max 1 time∈Icc (1:ℝ) 2 :=
      ⟨le_max_left _ _,max_le (by norm_num) h⟩
    have htime' : time∈Icc (0:ℝ) 2 := ⟨htime,h⟩
    simp [actualStateCost,actualHeldThenClockPath,hs,htime']
  · have hs : max 1 time∉Icc (1:ℝ) 2 := by
      intro hs
      exact h ((le_max_right _ _).trans hs.2)
    have htime' : time∉Icc (0:ℝ) 2 := fun ht=>h ht.2
    simp [actualStateCost,actualHeldThenClockPath,hs,htime']

theorem actual_backup_and_stitched_costs_are_genuinely_integrable_on_the_future_domain :
    IntegrableOn (fun t=>actualStateCost (actualClockBackupPath t 1)) (Ici (0:ℝ)) ∧
      IntegrableOn (fun t=>actualStateCost (actualHeldThenClockPath t)) (Ici (0:ℝ)) := by
  have hunit : Integrable ((Icc (0:ℝ) 1).indicator (fun _=> (3/4:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hdouble : Integrable ((Icc (0:ℝ) 2).indicator (fun _=> (3/4:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  constructor
  · rw [actual_clock_backup_cost_is_an_actual_unit_interval_indicator]
    exact hunit.integrableOn
  · apply hdouble.integrableOn.congr_fun _ measurableSet_Ici
    intro time ht
    exact (actual_stitched_state_cost_on_future_times_is_the_double_interval_indicator time ht).symm

theorem actual_two_individually_within_budget_parts_have_over_budget_stitched_total :
    (∫ t in Ico (0:ℝ) 1,actualStateCost (actualHeldThenClockPath t))=3/4 ∧
      (∫ t in Ici (0:ℝ),actualStateCost (actualClockBackupPath t 1))=3/4 ∧
      (∫ t in Ici (0:ℝ),actualStateCost (actualHeldThenClockPath t))=3/2 ∧
      (∫ t in Ico (0:ℝ) 1,actualStateCost (actualHeldThenClockPath t)) ≤ 1 ∧
      (∫ t in Ici (0:ℝ),actualStateCost (actualClockBackupPath t 1)) ≤ 1 ∧
      (1:ℝ)<(∫ t in Ici (0:ℝ),actualStateCost (actualHeldThenClockPath t)) := by
  have hp : (∫ t in Ico (0:ℝ) 1,actualStateCost (actualHeldThenClockPath t))=3/4 := by
    calc
      _ = ∫ _t in Ico (0:ℝ) 1,(3/4:ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro t ht
        have hm : max (1:ℝ) t=1 := max_eq_left ht.2.le
        norm_num [actualStateCost,actualHeldThenClockPath,hm]
      _ = _ := by norm_num [setIntegral_const,smul_eq_mul]
  have hb : (∫ t in Ici (0:ℝ),actualStateCost (actualClockBackupPath t 1))=3/4 := by
    rw [actual_clock_backup_cost_is_an_actual_unit_interval_indicator,setIntegral_indicator measurableSet_Icc]
    have hs : Ici (0:ℝ)∩Icc 0 1=Icc 0 1 := by ext t;simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc];tauto
    rw [hs]
    norm_num [setIntegral_const,smul_eq_mul]
  have hc : (∫ t in Ici (0:ℝ),actualStateCost (actualHeldThenClockPath t))=3/2 := by
    calc
      _ = ∫ t in Ici (0:ℝ),(Icc (0:ℝ) 2).indicator (fun _=> (3/4:ℝ)) t := by
        apply setIntegral_congr_fun measurableSet_Ici
        exact fun t ht=>actual_stitched_state_cost_on_future_times_is_the_double_interval_indicator t ht
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Icc]
        have hs : Ici (0:ℝ)∩Icc 0 2=Icc 0 2 := by ext t;simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc];tauto
        rw [hs]
        norm_num [setIntegral_const,smul_eq_mul]
  exact ⟨hp,hb,hc,by rw [hp];norm_num,by rw [hb];norm_num,by rw [hc];norm_num⟩

end SafeLearning.CompleteModulesGoSafeBudgetComposition
