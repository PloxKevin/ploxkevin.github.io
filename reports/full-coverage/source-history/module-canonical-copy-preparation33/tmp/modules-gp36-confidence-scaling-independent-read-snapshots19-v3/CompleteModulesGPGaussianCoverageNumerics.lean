import SafeLearning.CompleteModulesGPCorrectionNumerics
import SafeLearning.CompleteModulesGPGaussianCoverageFailure
import SafeLearning.CompleteAppliedGaussianTailIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPGaussianCoverageNumerics
open CompleteModulesGPCorrectionNumerics CompleteModulesGPGaussianCoverageFailure
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianTailIntegral

def scaledCorrectedWidth (R delta lambda c : ℝ) : ℝ :=
  (R/Real.sqrt (c*lambda))*Real.sqrt (Real.log (1+1/lambda)-2*Real.log delta)*
    Real.sqrt (c*lambda/(1+lambda))

theorem actual_corrected_one_point_half_width_is_the_literal_scale_independent_formula
    (R delta lambda c : ℝ) (hlambda : 0<lambda) (hc : 0<c) :
    scaledCorrectedWidth R delta lambda c=
      R*Real.sqrt (Real.log (1+1/lambda)-2*Real.log delta)/Real.sqrt (1+lambda) := by
  have ha : Real.sqrt (c*lambda)≠0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos hc hlambda))
  have hb : Real.sqrt (1+lambda)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  unfold scaledCorrectedWidth
  rw [Real.sqrt_div (mul_pos hc hlambda).le]
  field_simp

def originalRadius : ℝ := (3/2)*originalWidth 1 (1/20) (1/2) (1/10000)
def correctedHalfWidth : ℝ := Real.sqrt (Real.log 3-2*Real.log (1/20))/Real.sqrt (3/2)
def correctedRadius : ℝ := (3/2)*correctedHalfWidth
def correctedCoverage : ℝ :=
  (gaussianReal 0 1).real {epsilon | |epsilon/(3/2)|≤correctedHalfWidth}

theorem actual_corrected_half_width_at_the_printed_parameters_for_every_scale
    (c : ℝ) (hc : 0<c) :
    scaledCorrectedWidth 1 (1/20) (1/2) c=correctedHalfWidth := by
  rw [actual_corrected_one_point_half_width_is_the_literal_scale_independent_formula
    1 (1/20) (1/2) c (by norm_num) hc]
  norm_num [correctedHalfWidth]

theorem actual_original_standardized_radius_decimal_enclosure :
    (2119/100000:ℝ)<originalRadius ∧ originalRadius<(2120/100000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  have hlog : 0≤Real.log (10001/10000:ℝ) := Real.log_nonneg (by norm_num)
  have hup := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10001/10000)
  have ha : 0≤Real.log (10001/10000:ℝ)-2*Real.log (1/20) := by linarith
  have hsq : originalRadius^2=
      (3/40000)*(Real.log (10001/10000)-2*Real.log (1/20)) := by
    unfold originalRadius originalWidth
    norm_num [mul_pow,Real.sq_sqrt ha]
    ring
  have hn : 0≤originalRadius := by unfold originalRadius originalWidth;positivity
  constructor <;> nlinarith

theorem actual_corrected_half_width_decimal_enclosure :
    (217410/100000:ℝ)<correctedHalfWidth ∧ correctedHalfWidth<(217411/100000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  have ht := Real.log_three_gt_d9
  have hb := Real.log_three_lt_d9
  have ha : 0≤Real.log 3-2*Real.log (1/20) := by linarith
  have hsq : correctedHalfWidth^2=(2/3)*(Real.log 3-2*Real.log (1/20)) := by
    unfold correctedHalfWidth
    rw [div_pow,Real.sq_sqrt ha,Real.sq_sqrt (by norm_num : (0:ℝ)≤3/2)]
    ring
  have hn : 0≤correctedHalfWidth := by unfold correctedHalfWidth;positivity
  constructor <;> nlinarith

theorem actual_corrected_half_width_printed_two_decimal_rounding :
    |correctedHalfWidth-(217/100:ℝ)|<1/200 := by
  obtain ⟨hl,hu⟩ := actual_corrected_half_width_decimal_enclosure
  rw [abs_lt];constructor <;> linarith

theorem actual_corrected_standardized_radius_decimal_enclosure :
    (326115/100000:ℝ)<correctedRadius ∧ correctedRadius<(326116/100000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  have ht := Real.log_three_gt_d9
  have hb := Real.log_three_lt_d9
  have ha : 0≤Real.log 3-2*Real.log (1/20) := by linarith
  have hsq : correctedRadius^2=(3/2)*(Real.log 3-2*Real.log (1/20)) := by
    unfold correctedRadius correctedHalfWidth
    simp only [mul_pow,div_pow,Real.sq_sqrt ha,Real.sq_sqrt (by norm_num : (0:ℝ)≤3/2)]
    ring
  have hn : 0≤correctedRadius := by unfold correctedRadius correctedHalfWidth;positivity
  constructor <;> nlinarith

theorem actual_cdf_original_radius_rational_endpoint_enclosures :
    (50845/100000:ℝ)<standardCDF (2119/100000:ℝ) ∧
      standardCDF (2120/100000:ℝ)<(50846/100000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_integral_uniform_rational_error
    (2119/100000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_integral_uniform_rational_error
    (2120/100000:ℝ) (by constructor <;> norm_num)
  have hpa : (21188414331/1000000000000:ℝ)<actualPolynomialIntegral (2119/100000:ℝ) ∧
      actualPolynomialIntegral (2119/100000:ℝ)<21188414332/1000000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (21198412085/1000000000000:ℝ)<actualPolynomialIntegral (2120/100000:ℝ) ∧
      actualPolynomialIntegral (2120/100000:ℝ)<21198412086/1000000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_cdf_corrected_radius_rational_endpoint_enclosures :
    (999445/1000000:ℝ)<standardCDF (326115/100000:ℝ) ∧
      standardCDF (326116/100000:ℝ)<(1998891/2000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (326115/100000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (326116/100000:ℝ) (by constructor <;> norm_num)
  have hpa : (1251923443348/1000000000000:ℝ)<actualTailPolynomialIntegral (326115/100000:ℝ) ∧
      actualTailPolynomialIntegral (326115/100000:ℝ)<1251923443349/1000000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (1251923492395/1000000000000:ℝ)<actualTailPolynomialIntegral (326116/100000:ℝ) ∧
      actualTailPolynomialIntegral (326116/100000:ℝ)<1251923492396/1000000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_original_coverage_is_the_true_cdf_at_the_derived_standardized_radius :
    actualCoverage 1 (1/20) (1/2) (1/10000)=2*standardCDF originalRadius-1 := by
  unfold actualCoverage originalRadius
  convert actual_gaussian_coverage_of_zero_is_the_true_two_sided_cdf
    1 (by norm_num) (1/2) (originalWidth 1 (1/20) (1/2) (1/10000))
    (by norm_num) (by unfold originalWidth;positivity) using 1 <;> norm_num

theorem actual_corrected_coverage_is_the_true_cdf_at_the_derived_standardized_radius :
    correctedCoverage=2*standardCDF correctedRadius-1 := by
  unfold correctedCoverage correctedRadius
  convert actual_gaussian_coverage_of_zero_is_the_true_two_sided_cdf
    1 (by norm_num) (1/2) correctedHalfWidth
    (by norm_num) (by unfold correctedHalfWidth;positivity) using 1 <;> norm_num

theorem actual_original_and_corrected_gaussian_coverage_decimal_enclosures :
    (169/10000:ℝ)<actualCoverage 1 (1/20) (1/2) (1/10000) ∧
      actualCoverage 1 (1/20) (1/2) (1/10000)<(1692/100000:ℝ) ∧
      (998890/1000000:ℝ)<correctedCoverage ∧ correctedCoverage<(998891/1000000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_original_standardized_radius_decimal_enclosure
  obtain ⟨ht,hb⟩ := actual_corrected_standardized_radius_decimal_enclosure
  obtain ⟨hcl,hcu⟩ := actual_cdf_original_radius_rational_endpoint_enclosures
  obtain ⟨hct,hcb⟩ := actual_cdf_corrected_radius_rational_endpoint_enclosures
  have hm := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hol := hm hl
  have hou := hm hu
  have htl := hm ht
  have htu := hm hb
  rw [actual_original_coverage_is_the_true_cdf_at_the_derived_standardized_radius,
    actual_corrected_coverage_is_the_true_cdf_at_the_derived_standardized_radius]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_original_and_corrected_gaussian_coverage_printed_three_decimal_roundings :
    |actualCoverage 1 (1/20) (1/2) (1/10000)-(17/1000:ℝ)|<1/2000 ∧
      |correctedCoverage-(999/1000:ℝ)|<1/2000 := by
  obtain ⟨hl,hu,ht,hb⟩ := actual_original_and_corrected_gaussian_coverage_decimal_enclosures
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_original_gaussian_coverage_violates_the_literal_ninety_five_percent_claim :
    actualCoverage 1 (1/20) (1/2) (1/10000)<(95/100:ℝ) ∧
      (95/100:ℝ)<correctedCoverage := by
  obtain ⟨hl,hu,ht,hb⟩ := actual_original_and_corrected_gaussian_coverage_decimal_enclosures
  constructor <;> linarith

end SafeLearning.CompleteModulesGPGaussianCoverageNumerics
