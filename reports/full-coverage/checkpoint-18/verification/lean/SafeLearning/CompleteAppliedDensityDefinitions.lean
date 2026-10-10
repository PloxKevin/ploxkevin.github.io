import SafeLearning.CompleteAppliedExpectations

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDensityDefinitions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
open SafeLearning.CompleteAppliedDensityScaling
open SafeLearning.CompleteAppliedExpectations

theorem actual_density_probability_of_a_measurable_event
    (density : ℝ → ℝ) (hmeasurable : Measurable density)
    (hnonnegative : ∀ x,0 ≤ density x) (event : Set ℝ) (hevent : MeasurableSet event) :
    (actualDensityLaw density).real event = ∫ x in event,density x := by
  rw [←integral_indicator_one hevent,
    actual_density_law_expectation_is_the_density_weighted_integral
      density hmeasurable hnonnegative]
  have he : (fun x => density x*event.indicator (fun _ => (1:ℝ)) x) = event.indicator density := by
    funext x
    by_cases hx : x ∈ event <;> simp [hx]
  calc
    _ = ∫ x,event.indicator density x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrFun he x)
    _ = _ := integral_indicator hevent

theorem actual_density_single_point_probability_is_zero
    (density : ℝ → ℝ) (point : ℝ) : (actualDensityLaw density) {point}=0 := by
  unfold actualDensityLaw
  exact measure_singleton point

def actualHalfMixedLaw (point : ℝ) (density : ℝ → ℝ) : Measure ℝ :=
  (1/2:ℝ≥0∞) • Measure.dirac point + (1/2:ℝ≥0∞) • actualDensityLaw density

theorem actual_half_mixed_law_is_normalized_and_has_a_true_atom_and_density_part
    (point : ℝ) (density : ℝ → ℝ)
    (hnonnegative : ∀ x,0 ≤ density x) (hintegrable : Integrable density volume)
    (hnormalized : (∫ x,density x)=1) :
    IsProbabilityMeasure (actualHalfMixedLaw point density) ∧
      actualHalfMixedLaw point density {point}=(1/2:ℝ≥0∞) ∧
      (1/2:ℝ≥0∞) • actualDensityLaw density ≠ 0 := by
  have hp := actual_normalized_nonnegative_density_is_a_probability_law
    density hnonnegative hintegrable hnormalized
  let : IsProbabilityMeasure (actualDensityLaw density) := hp
  constructor
  · constructor
    simp only [actualHalfMixedLaw,Measure.add_apply,Measure.smul_apply,
      measure_univ,smul_eq_mul,mul_one]
    rw [←ENNReal.add_div]
    norm_num only [one_add_one_eq_two]
    exact ENNReal.div_self (by norm_num) (by simp)
  constructor
  · simp [actualHalfMixedLaw,Measure.add_apply,Measure.smul_apply,
      actual_density_single_point_probability_is_zero]
  · intro hzero
    have h := congrArg (fun law : Measure ℝ => law univ) hzero
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] at h
    norm_num at h

end SafeLearning.CompleteAppliedDensityDefinitions
