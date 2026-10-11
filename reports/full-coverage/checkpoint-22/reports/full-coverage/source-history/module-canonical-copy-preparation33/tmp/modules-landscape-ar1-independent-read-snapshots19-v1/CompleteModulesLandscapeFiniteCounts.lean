import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeFiniteCounts
variable {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}

def stepCost (event : Set Ω) (ω : Ω) : ℝ := event.indicator (fun _=>1) ω
def unsafeCount (events : Fin (T+1)→Set Ω) (ω : Ω) : ℝ := ∑ time,stepCost (events time) ω
def everUnsafe (events : Fin (T+1)→Set Ω) : Set Ω := ⋃ time,events time

theorem actual_step_cost_is_the_zero_one_source_indicator (event : Set Ω) (ω : Ω) :
    (ω∈event → stepCost event ω=1) ∧ (ω∉event → stepCost event ω=0) := by
  classical
  simp [stepCost,Set.indicator]

theorem actual_indicator_count_bounds_and_union_bridge (events : Fin (T+1)→Set Ω) (ω : Ω) :
    0≤ unsafeCount events ω ∧
    stepCost (everUnsafe events) ω≤ unsafeCount events ω ∧
    unsafeCount events ω≤ (T+1:ℝ)*stepCost (everUnsafe events) ω := by
  classical
  have hcost (time : Fin (T+1)) : 0≤ stepCost (events time) ω ∧ stepCost (events time) ω≤1 := by
    by_cases h : ω∈events time <;> simp [stepCost,Set.indicator,h]
  refine ⟨Finset.sum_nonneg (fun time _=>(hcost time).1),?_,?_⟩
  · by_cases h : ω∈everUnsafe events
    · obtain ⟨time,ht⟩ : ∃ time,ω∈events time := by simpa [everUnsafe] using h
      rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).1 h]
      have hs := Finset.single_le_sum (fun t _=>(hcost t).1) (Finset.mem_univ time)
      rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).1 ht] at hs
      exact hs
    · rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).2 h]
      exact Finset.sum_nonneg (fun time _=>(hcost time).1)
  · by_cases h : ω∈everUnsafe events
    · rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).1 h,mul_one]
      have hs := Finset.sum_le_sum (fun time (_ : time∈Finset.univ)=>(hcost time).2)
      simpa [unsafeCount] using hs
    · have he (time : Fin (T+1)) : ω∉events time := by
        intro ht;exact h (mem_iUnion.mpr ⟨time,ht⟩)
      simp [unsafeCount,stepCost,Set.indicator,he,h]

theorem actual_count_and_event_indicators_are_integrable
    (P : Measure Ω) [IsProbabilityMeasure P] (events : Fin (T+1)→Set Ω)
    (hmeas : ∀ time,MeasurableSet (events time)) :
    Integrable (unsafeCount events) P ∧ Integrable (stepCost (everUnsafe events)) P := by
  constructor
  · exact integrable_finset_sum _ (fun time _=>(integrable_const (1:ℝ)).indicator (hmeas time))
  · exact (integrable_const (1:ℝ)).indicator (MeasurableSet.iUnion hmeas)

theorem actual_expected_indicator_count_is_sum_of_marginal_probabilities
    (P : Measure Ω) [IsProbabilityMeasure P] (events : Fin (T+1)→Set Ω)
    (hmeas : ∀ time,MeasurableSet (events time)) :
    (∫ ω,unsafeCount events ω ∂P)=∑ time,P.real (events time) := by
  change (∫ ω,∑ time : Fin (T+1),stepCost (events time) ω ∂P)=∑ time,P.real (events time)
  rw [integral_finsetSum Finset.univ (μ:=P) (f:=fun time ω=>stepCost (events time) ω)
    (fun time _=>(integrable_const (1:ℝ)).indicator (hmeas time))]
  apply Finset.sum_congr rfl
  intro time _
  exact integral_indicator_one (hmeas time)

theorem actual_failure_probability_and_expected_count_control_each_other_only_up_to_horizon
    (P : Measure Ω) [IsProbabilityMeasure P] (events : Fin (T+1)→Set Ω)
    (hmeas : ∀ time,MeasurableSet (events time)) :
    P.real (everUnsafe events)≤ (∫ ω,unsafeCount events ω ∂P) ∧
    (∫ ω,unsafeCount events ω ∂P)≤ (T+1:ℝ)*P.real (everUnsafe events) := by
  have hi := actual_count_and_event_indicators_are_integrable P events hmeas
  have he : (∫ ω,stepCost (everUnsafe events) ω ∂P)=P.real (everUnsafe events) :=
    integral_indicator_one (MeasurableSet.iUnion hmeas)
  constructor
  · rw [←he]
    exact integral_mono hi.2 hi.1 (fun ω=>(actual_indicator_count_bounds_and_union_bridge events ω).2.1)
  · have hc := integral_mono hi.1 (hi.2.const_mul (T+1:ℝ))
      (fun ω=>(actual_indicator_count_bounds_and_union_bridge events ω).2.2)
    rw [integral_const_mul,he] at hc
    exact hc

def exactlyOneUnsafeStep (failure : Set Ω) : Fin (T+1)→Set Ω := fun time=>if time=0 then failure else ∅
def everyUnsafeStep (failure : Set Ω) : Fin (T+1)→Set Ω := fun _=>failure

theorem actual_one_step_and_every_step_trajectories_attain_both_bounds (failure : Set Ω) :
    everUnsafe (exactlyOneUnsafeStep (T:=T) failure)=failure ∧
    unsafeCount (exactlyOneUnsafeStep (T:=T) failure)=stepCost failure ∧
    everUnsafe (everyUnsafeStep (T:=T) failure)=failure ∧
    unsafeCount (everyUnsafeStep (T:=T) failure)=fun ω=>(T+1:ℝ)*stepCost failure ω := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · ext ω
    simp [everUnsafe,exactlyOneUnsafeStep]
  · funext ω
    have he (time : Fin (T+1)) :
        stepCost (exactlyOneUnsafeStep failure time) ω=if time=0 then stepCost failure ω else 0 := by
      by_cases h : time=0 <;> simp [exactlyOneUnsafeStep,stepCost,h]
    simp only [unsafeCount,he]
    simp
  · ext ω
    simp [everUnsafe,everyUnsafeStep]
  · funext ω
    simp [unsafeCount,everyUnsafeStep]

theorem actual_both_indicator_count_probability_bounds_are_genuinely_tight
    (P : Measure Ω) [IsProbabilityMeasure P] (failure : Set Ω) (hmeas : MeasurableSet failure) :
    (∫ ω,unsafeCount (exactlyOneUnsafeStep (T:=T) failure) ω ∂P)=P.real failure ∧
    P.real (everUnsafe (exactlyOneUnsafeStep (T:=T) failure))=P.real failure ∧
    (∫ ω,unsafeCount (everyUnsafeStep (T:=T) failure) ω ∂P)=(T+1:ℝ)*P.real failure ∧
    P.real (everUnsafe (everyUnsafeStep (T:=T) failure))=P.real failure := by
  have h := actual_one_step_and_every_step_trajectories_attain_both_bounds (T:=T) failure
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
  have hi : (∫ ω,stepCost failure ω ∂P)=P.real failure := integral_indicator_one hmeas
  rw [integral_const_mul,hi]
  simp

theorem actual_every_expected_count_budget_at_least_one_accepts_certain_failure
    (P : Measure Ω) [IsProbabilityMeasure P] (budget : ℝ) (hbudget : 1≤ budget) :
    (∫ ω,unsafeCount (exactlyOneUnsafeStep (T:=T) Set.univ) ω ∂P)≤ budget ∧
    P.real (everUnsafe (exactlyOneUnsafeStep (T:=T) Set.univ))=1 := by
  have h := actual_both_indicator_count_probability_bounds_are_genuinely_tight
    (T:=T) P Set.univ MeasurableSet.univ
  have hu : P.real Set.univ=1 := by simp
  rw [hu] at h
  exact ⟨h.1.le.trans hbudget,h.2.1⟩

end SafeLearning.CompleteModulesLandscapeFiniteCounts
