import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDiscreteMassDefinitions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Value : Type*} [MeasurableSpace Value] [MeasurableSingletonClass Value]

def actualDiscreteMass (law : Measure Value) (value : Value) : ℝ := law.real {value}

theorem actual_countable_probability_law_has_normalized_nonnegative_atom_masses
    [Countable Value] (law : Measure Value) [IsProbabilityMeasure law] :
    (∀ value,0 ≤ actualDiscreteMass law value) ∧
      Summable (actualDiscreteMass law) ∧ (∑' value,actualDiscreteMass law value)=1 := by
  have hsum : (∑' value : Value,law {value})=1 := by
    simpa using law.tsum_indicator_apply_singleton univ MeasurableSet.univ
  constructor
  · intro value
    exact ENNReal.toReal_nonneg
  constructor
  · exact ENNReal.summable_toReal (by rw [hsum]; norm_num)
  · change (∑' value : Value,(law {value}).toReal)=1
    rw [←ENNReal.tsum_toReal_eq (fun _ => measure_ne_top law _),hsum]
    norm_num

theorem actual_countable_probability_of_an_event_is_the_sum_of_its_atom_masses
    [Countable Value] (law : Measure Value) [IsProbabilityMeasure law]
    (event : Set Value) (hevent : MeasurableSet event) :
    (∑' value,event.indicator (actualDiscreteMass law) value)=law.real event := by
  have he : (fun value => (event.indicator (fun x => law {x}) value).toReal)=
      event.indicator (actualDiscreteMass law) := by
    funext value
    by_cases hvalue : value ∈ event <;> simp [hvalue,actualDiscreteMass,measureReal_def]
  rw [←he,←ENNReal.tsum_toReal_eq]
  · rw [law.tsum_indicator_apply_singleton event hevent,measureReal_def]
  · intro value
    by_cases hvalue : value ∈ event <;> simp [hvalue,measure_ne_top]

def actualBernoulliLaw (parameter : unitInterval) : Measure ℝ :=
  bernoulliMeasure 1 0 parameter

theorem actual_bernoulli_law_is_a_probability_and_has_the_printed_atom_masses
    (parameter : unitInterval) :
    IsProbabilityMeasure (actualBernoulliLaw parameter) ∧
      (actualBernoulliLaw parameter).real {1}=(parameter:ℝ) ∧
      (actualBernoulliLaw parameter).real {0}=1-(parameter:ℝ) := by
  constructor
  · unfold actualBernoulliLaw
    infer_instance
  constructor <;>
    rw [actualBernoulliLaw,bernoulliMeasure_real_apply parameter (measurableSet_singleton _)]
  · norm_num
  · norm_num [unitInterval.coe_symm_eq]

theorem actual_bernoulli_law_is_supported_on_zero_and_one
    (parameter : unitInterval) : actualBernoulliLaw parameter {0,1}=1 := by
  unfold actualBernoulliLaw
  exact bernoulliMeasure_apply_of_mem_of_mem parameter (by measurability) (by simp) (by simp)

theorem actual_point_mass_initial_law_means_the_initial_state_is_always_the_given_state
    (initial : Value) :
    IsProbabilityMeasure (Measure.dirac initial) ∧
      (Measure.dirac initial).real {initial}=1 ∧
      ∀ᵐ value ∂Measure.dirac initial,value=initial := by
  exact ⟨inferInstance,by simp,by simp⟩

end SafeLearning.CompleteAppliedDiscreteMassDefinitions
