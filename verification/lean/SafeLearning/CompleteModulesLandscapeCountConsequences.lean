import SafeLearning.CompleteModulesLandscapeFiniteCounts
import SafeLearning.CompleteAppliedDiscreteMassDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeCountConsequences
open CompleteModulesLandscapeFiniteCounts CompleteAppliedDiscreteMassDefinitions

theorem actual_source_event_is_exactly_the_count_at_least_one_event
    {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} (events : Fin (T+1)→Set Ω) :
    everUnsafe events={ω | (1:ℝ)≤ unsafeCount events ω} := by
  classical
  ext ω
  have hb := actual_indicator_count_bounds_and_union_bridge events ω
  constructor
  · intro h
    rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).1 h] at hb
    exact hb.2.1
  · intro h
    change (1:ℝ) ≤ unsafeCount events ω at h
    by_contra hn
    rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).2 hn] at hb
    simp only [mul_zero] at hb
    linarith [hb.2.2]

theorem actual_chance_budget_implies_only_the_horizon_scaled_expected_count_bound
    {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (events : Fin (T+1)→Set Ω)
    (hmeas : ∀ time,MeasurableSet (events time)) (delta : ℝ)
    (hchance : P.real (everUnsafe events)≤ delta) :
    (∫ ω,unsafeCount events ω ∂P)≤ (T+1:ℝ)*delta := by
  exact (actual_failure_probability_and_expected_count_control_each_other_only_up_to_horizon
    P events hmeas).2.trans (mul_le_mul_of_nonneg_left hchance (by positivity))

theorem actual_every_failure_probability_has_both_tight_trajectory_laws
    (T : ℕ) (p : ℝ) (hp : 0≤ p) (hp1 : p≤1) :
    ∃ P : Measure ℝ,IsProbabilityMeasure P ∧
      P.real (everUnsafe (exactlyOneUnsafeStep (T:=T) {1}))=p ∧
      (∫ ω,unsafeCount (exactlyOneUnsafeStep (T:=T) {1}) ω ∂P)=p ∧
      P.real (everUnsafe (everyUnsafeStep (T:=T) {1}))=p ∧
      (∫ ω,unsafeCount (everyUnsafeStep (T:=T) {1}) ω ∂P)=(T+1:ℝ)*p := by
  let parameter : unitInterval := ⟨p,⟨hp,hp1⟩⟩
  let P : Measure ℝ := actualBernoulliLaw parameter
  have hP := actual_bernoulli_law_is_a_probability_and_has_the_printed_atom_masses parameter
  letI : IsProbabilityMeasure P := hP.1
  have h := actual_both_indicator_count_probability_bounds_are_genuinely_tight
    (T:=T) P {1} (measurableSet_singleton 1)
  have hmass : P.real {1}=p := hP.2.1
  rw [hmass] at h
  exact ⟨P,hP.1,h.2.1,h.1,h.2.2.2,h.2.2.1⟩

def sourceRandomTimeLaw (T : ℕ) : PMF (Fin (T+1)) := PMF.uniformOfFintype (Fin (T+1))
def sourceRandomTimeEvents (T : ℕ) : Fin (T+1)→Set (Fin (T+1)) := fun time=>{time}

theorem actual_uniform_random_failure_time_always_has_exactly_one_violation
    (T : ℕ) :
    (∀ ω : Fin (T+1),unsafeCount (sourceRandomTimeEvents T) ω=1) ∧
    everUnsafe (sourceRandomTimeEvents T)=Set.univ ∧
    (∫ ω,unsafeCount (sourceRandomTimeEvents T) ω ∂(sourceRandomTimeLaw T).toMeasure)=1 ∧
    (sourceRandomTimeLaw T).toMeasure.real (everUnsafe (sourceRandomTimeEvents T))=1 := by
  classical
  have hcount (ω : Fin (T+1)) : unsafeCount (sourceRandomTimeEvents T) ω=1 := by
    simp [unsafeCount,sourceRandomTimeEvents,stepCost,Set.indicator,eq_comm]
  have hevent : everUnsafe (sourceRandomTimeEvents T)=Set.univ := by
    ext ω
    simp [everUnsafe,sourceRandomTimeEvents]
  refine ⟨hcount,hevent,?_,?_⟩
  · simp only [hcount]
    simp
  · rw [hevent]
    simp

theorem actual_uniform_random_time_example_passes_every_count_budget_at_least_one
    (T : ℕ) (budget : ℝ) (hbudget : 1≤ budget) :
    (∫ ω,unsafeCount (sourceRandomTimeEvents T) ω ∂(sourceRandomTimeLaw T).toMeasure)≤ budget ∧
    (sourceRandomTimeLaw T).toMeasure.real (everUnsafe (sourceRandomTimeEvents T))=1 := by
  have h := actual_uniform_random_failure_time_always_has_exactly_one_violation T
  exact ⟨h.2.2.1.le.trans hbudget,h.2.2.2⟩

end SafeLearning.CompleteModulesLandscapeCountConsequences
