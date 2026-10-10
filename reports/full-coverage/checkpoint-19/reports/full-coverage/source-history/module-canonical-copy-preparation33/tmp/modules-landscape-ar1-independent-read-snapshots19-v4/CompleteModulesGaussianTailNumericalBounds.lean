import SafeLearning.CompleteAppliedGaussianTailIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesGaussianTailNumericalBounds
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianTailIntegral

theorem actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
    (r lower upper : ℝ) (hr : r∈Icc (0:ℝ) 4)
    (hpoly : 0 ≤ actualTailPolynomialIntegral r-1/2500000000000000)
    (hlower : lower < 1/2-(3989424/10000000)*(actualTailPolynomialIntegral r+1/2500000000000000))
    (hupper : 1/2-(3989422/10000000)*(actualTailPolynomialIntegral r-1/2500000000000000) < upper) :
    lower < 1-standardCDF r ∧ 1-standardCDF r < upper := by
  have hc := actual_standard_gaussian_normalization_rational_enclosure
  have hi := actual_gaussian_exponential_tail_integral_uniform_rational_error r hr
  have hl : actualTailPolynomialIntegral r-1/2500000000000000 ≤
      ∫x in (0:ℝ)..r, Real.exp (-x^2/2) := by have h := (abs_le.mp hi).1; linarith
  have hu : (∫x in (0:ℝ)..r, Real.exp (-x^2/2)) ≤
      actualTailPolynomialIntegral r+1/2500000000000000 := by have h := (abs_le.mp hi).2; linarith
  have hn : 0 ≤ (∫x in (0:ℝ)..r, Real.exp (-x^2/2)) := hpoly.trans hl
  have hcm : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹ := by positivity
  have hmulU := (mul_le_mul_of_nonneg_right hc.2.le hn).trans
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 3989424/10000000))
  have hmulL := (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 3989422/10000000)).trans
    (mul_le_mul_of_nonneg_right hc.1.le hn)
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> linarith

theorem actual_gaussian_upper_tail_is_antitone : Antitone (fun r : ℝ => 1-standardCDF r) := by
  intro x y hxy
  have h := measureReal_mono (μ := gaussianReal 0 1) (Iic_subset_Iic.mpr hxy)
  change standardCDF x ≤ standardCDF y at h
  linarith

theorem actual_positive_denominator_squared_bounds_give_true_standardized_bounds
    (numerator variance lower upper : ℝ) (hn : 0 < numerator) (hv : 0 < variance)
    (hl : 0 ≤ lower) (hu : 0 < upper)
    (hlower : lower^2*variance < numerator^2) (hupper : numerator^2 < upper^2*variance) :
    lower < numerator/Real.sqrt variance ∧ numerator/Real.sqrt variance < upper := by
  have hs : 0 < Real.sqrt variance := Real.sqrt_pos_of_pos hv
  have hsq : (Real.sqrt variance)^2 = variance := Real.sq_sqrt hv.le
  constructor
  · rw [lt_div_iff₀ hs]
    have h : (lower*Real.sqrt variance)^2 < numerator^2 := by rw [mul_pow, hsq]; exact hlower
    have hnonneg := mul_nonneg hl hs.le
    nlinarith
  · rw [div_lt_iff₀ hs]
    have h : numerator^2 < (upper*Real.sqrt variance)^2 := by rw [mul_pow, hsq]; exact hupper
    have hpos := mul_pos hu hs
    nlinarith

theorem actual_standardized_tail_inherits_both_true_endpoint_probability_bounds
    (z lowerRadius upperRadius lowerProbability upperProbability : ℝ)
    (hz : lowerRadius ≤ z ∧ z ≤ upperRadius)
    (hl : lowerProbability < 1-standardCDF upperRadius)
    (hu : 1-standardCDF lowerRadius < upperProbability) :
    lowerProbability < 1-standardCDF z ∧ 1-standardCDF z < upperProbability :=
  ⟨hl.trans_le (actual_gaussian_upper_tail_is_antitone hz.2),
    (actual_gaussian_upper_tail_is_antitone hz.1).trans_lt hu⟩

end SafeLearning.CompleteModulesGaussianTailNumericalBounds
