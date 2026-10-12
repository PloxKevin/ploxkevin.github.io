import SafeLearning.CompleteAppliedExpectations

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedExpectationDomains
open MeasureTheory
open scoped ENNReal
open SafeLearning.CompleteAppliedExpectations
open SafeLearning.CompleteAppliedDensityScaling

variable {Value : Type*} [MeasurableSpace Value]

theorem actual_countable_absolute_integrability_is_the_weighted_absolute_sum_finite
    [Countable Value] [MeasurableSingletonClass Value]
    (law : Measure Value) (quantity : Value → ℝ) (hquantity : Measurable quantity) :
    Integrable quantity law ↔
      (∑' value,ENNReal.ofReal |quantity value| * law {value}) < ∞ := by
  rw [actual_integrability_is_finiteness_of_the_absolute_mean law quantity hquantity,
    lintegral_countable']

theorem actual_density_absolute_integrability_is_the_weighted_quantity_integrable
    (density : ℝ → ℝ) (hdensity : Measurable density)
    (hnonnegative : ∀ x,0 ≤ density x) (quantity : ℝ → ℝ) :
    Integrable quantity (actualDensityLaw density) ↔
      Integrable (fun x => density x*quantity x) volume := by
  unfold actualDensityLaw
  rw [integrable_withDensity_iff_integrable_smul' hdensity.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnonnegative _),smul_eq_mul]

theorem actual_density_absolute_integrability_is_the_weighted_absolute_integral_finite
    (density : ℝ → ℝ) (hdensity : Measurable density)
    (hnonnegative : ∀ x,0 ≤ density x) (quantity : ℝ → ℝ)
    (hquantity : Measurable quantity) :
    Integrable quantity (actualDensityLaw density) ↔
      (∫⁻ x,ENNReal.ofReal (density x*|quantity x|)) < ∞ := by
  rw [actual_density_absolute_integrability_is_the_weighted_quantity_integrable
    density hdensity hnonnegative quantity,
    actual_integrability_is_finiteness_of_the_absolute_mean volume
      (fun x => density x*quantity x) (hdensity.mul hquantity)]
  simp only [abs_mul,abs_of_nonneg (hnonnegative _)]

end SafeLearning.CompleteAppliedExpectationDomains
