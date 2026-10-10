import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedProbabilitySpace
open MeasureTheory ProbabilityTheory Set
open scoped Function ENNReal

variable {Omega Value : Type*} [MeasurableSpace Omega] [MeasurableSpace Value]

def actualLaw (measure : Measure Omega) (randomVariable : Omega → Value) : Measure Value :=
  measure.map randomVariable

theorem actual_events_are_closed_under_complement_and_countable_union
    (events : ℕ → Set Omega) (hmeasurable : ∀ n,MeasurableSet (events n)) :
    (∀ n,MeasurableSet (events n)ᶜ) ∧ MeasurableSet (⋃ n,events n) := by
  exact ⟨fun n => (hmeasurable n).compl,MeasurableSet.iUnion hmeasurable⟩

theorem actual_probability_is_in_the_unit_interval
    (measure : Measure Omega) [IsProbabilityMeasure measure] (event : Set Omega) :
    0 ≤ measure.real event ∧ measure.real event ≤ 1 := by
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

theorem actual_total_probability_is_one
    (measure : Measure Omega) [IsProbabilityMeasure measure] :
    measure.real (univ : Set Omega)=1 := probReal_univ

theorem actual_countable_disjoint_event_probabilities_are_summable_and_add
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (events : ℕ → Set Omega) (hmeasurable : ∀ n,MeasurableSet (events n))
    (hdisjoint : Pairwise (Disjoint on events)) :
    Summable (fun n => measure.real (events n)) ∧
      measure.real (⋃ n,events n)=∑' n,measure.real (events n) := by
  have he := measure_iUnion hdisjoint hmeasurable (μ := measure)
  have hs : (∑' n,measure (events n)) ≠ ∞ := by
    rw [←he]
    exact measure_ne_top _ _
  refine ⟨ENNReal.summable_toReal hs,?_⟩
  change (measure (⋃ n,events n)).toReal = _
  rw [he,ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  rfl

theorem actual_probability_complement_and_monotonicity
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (event larger : Set Omega) (hmeasurable : MeasurableSet event)
    (hsubset : event ⊆ larger) :
    measure.real eventᶜ=1-measure.real event ∧
      measure.real event ≤ measure.real larger := by
  exact ⟨probReal_compl_eq_one_sub hmeasurable,measureReal_mono hsubset⟩

theorem actual_law_is_the_true_event_pushforward
    (measure : Measure Omega) (randomVariable : Omega → Value)
    (hmeasurable : Measurable randomVariable) (event : Set Value) (hevent : MeasurableSet event) :
    actualLaw measure randomVariable event=measure (randomVariable ⁻¹' event) ∧
      (actualLaw measure randomVariable).real event=measure.real (randomVariable ⁻¹' event) := by
  have he : actualLaw measure randomVariable event=measure (randomVariable ⁻¹' event) :=
    Measure.map_apply hmeasurable hevent
  exact ⟨he,congrArg ENNReal.toReal he⟩

theorem actual_random_variable_has_its_actual_probability_law
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (randomVariable : Omega → Value) (hmeasurable : Measurable randomVariable) :
    HasLaw randomVariable (actualLaw measure randomVariable) measure ∧
      IsProbabilityMeasure (actualLaw measure randomVariable) := by
  refine ⟨hasLaw_map hmeasurable.aemeasurable,?_⟩
  dsimp [actualLaw]
  infer_instance

theorem actual_random_sequence_is_measurable_from_its_coordinates
    (sequence : ℕ → Omega → Value) (hmeasurable : ∀ n,Measurable (sequence n)) :
    Measurable (fun outcome n => sequence n outcome) :=
  Measurable.of_eval hmeasurable

end SafeLearning.CompleteAppliedProbabilitySpace
