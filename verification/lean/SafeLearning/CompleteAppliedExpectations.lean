import SafeLearning.CompleteAppliedDensityScaling
import SafeLearning.CompleteAppliedProbabilitySpace

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedExpectations
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
open SafeLearning.CompleteAppliedDensityScaling
open SafeLearning.CompleteAppliedProbabilitySpace

variable {Omega Value : Type*} [MeasurableSpace Omega] [MeasurableSpace Value]

theorem actual_integrability_is_finiteness_of_the_absolute_mean
    (measure : Measure Omega) (quantity : Omega → ℝ) (hmeasurable : Measurable quantity) :
    Integrable quantity measure ↔ (∫⁻ x,ENNReal.ofReal |quantity x| ∂measure) < ∞ := by
  simp only [Integrable,hmeasurable.aestronglyMeasurable,true_and,
    hasFiniteIntegral_iff_norm,Real.norm_eq_abs]

theorem actual_expectation_is_the_integral_under_the_true_law
    (measure : Measure Omega) (randomVariable : Omega → Value)
    (hmeasurable : Measurable randomVariable) (quantity : Value → ℝ)
    (hquantity : Measurable quantity) :
    (∫ outcome,quantity (randomVariable outcome) ∂measure) =
      ∫ value,quantity value ∂actualLaw measure randomVariable := by
  exact (hasLaw_map hmeasurable.aemeasurable).integral_comp hquantity.aestronglyMeasurable

theorem actual_countable_law_expectation_is_the_mass_weighted_sum
    [Countable Value] [MeasurableSingletonClass Value]
    (law : Measure Value) (quantity : Value → ℝ) (hintegrable : Integrable quantity law) :
    (∫ value,quantity value ∂law) = ∑' value,law.real {value} * quantity value := by
  simpa only [smul_eq_mul] using integral_countable hintegrable

theorem actual_density_law_expectation_is_the_density_weighted_integral
    (density : ℝ → ℝ) (hmeasurable : Measurable density)
    (hnonnegative : ∀ x,0 ≤ density x) (quantity : ℝ → ℝ) :
    (∫ x,quantity x ∂actualDensityLaw density) = ∫ x,density x*quantity x := by
  unfold actualDensityLaw
  rw [integral_withDensity_eq_integral_toReal_smul hmeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnonnegative _),smul_eq_mul]

theorem actual_expectation_linearity_without_independence
    (measure : Measure Omega) [IsProbabilityMeasure measure]
    (first second : Omega → ℝ) (hfirst : Integrable first measure)
    (hsecond : Integrable second measure) (left right constant : ℝ) :
    (∫ x,left*first x+right*second x+constant ∂measure) =
      left*(∫ x,first x ∂measure)+right*(∫ x,second x ∂measure)+constant := by
  have hf : Integrable (fun x => left*first x) measure := hfirst.const_mul left
  have hg : Integrable (fun x => right*second x) measure := hsecond.const_mul right
  have hs : Integrable (fun x => left*first x+right*second x) measure := hf.add hg
  rw [integral_add hs (integrable_const constant),
    integral_add hf hg,integral_const_mul,
    integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]

theorem actual_indicator_values_and_expectation
    (measure : Measure Omega) (event : Set Omega) (hmeasurable : MeasurableSet event) :
    (∀ outcome,event.indicator (fun _ => (1:ℝ)) outcome = if outcome ∈ event then 1 else 0) ∧
      (∫ outcome,event.indicator (fun _ => (1:ℝ)) outcome ∂measure)=measure.real event := by
  exact ⟨fun _ => rfl,integral_indicator_one hmeasurable⟩

theorem actual_positive_step_indicator_is_the_positive_event
    (value : ℝ) :
    (Ioi (0:ℝ)).indicator (fun _ => (1:ℝ)) value = if 0 < value then 1 else 0 := rfl

theorem actual_nonnegative_query_indicator_is_a_measurable_event
    (quantity : Omega → ℝ) (hmeasurable : Measurable quantity) :
    MeasurableSet {outcome | 0 ≤ quantity outcome} ∧
      Measurable ({outcome | 0 ≤ quantity outcome}.indicator (fun _ => (1:ℝ))) := by
  have hs : MeasurableSet {outcome | 0 ≤ quantity outcome} :=
    measurableSet_le measurable_const hmeasurable
  exact ⟨hs,measurable_const.indicator hs⟩

end SafeLearning.CompleteAppliedExpectations
