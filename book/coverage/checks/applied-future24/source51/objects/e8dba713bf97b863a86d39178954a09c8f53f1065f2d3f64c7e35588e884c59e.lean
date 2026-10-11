import SafeLearning.CompleteModulesLandscapeARStationaryGaussian
import SafeLearning.CompleteModulesLandscapeGaussianTailCounts
import SafeLearning.CompleteModulesGaussianTailNumericalBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SafeLearning.CompleteModulesLandscapeARStationaryNumerics
open CompleteModulesLandscapeARStationaryGaussian CompleteModulesLandscapeGaussianTailCounts
open CompleteAppliedGaussianCDF CompleteAppliedGaussianTailIntegral
open CompleteModulesGaussianTailNumericalBounds

def sourceStationarySD : ℝ := Real.sqrt (stationaryVariance (1/2) (1/10) : ℝ)
def sourceStationaryZ : ℝ := (1-4/5)/sourceStationarySD
def sourceStationaryTail : ℝ := (stationaryLaw (1/2) (4/5) (1/10)).real (Ioi 1)

theorem actual_literal_stationary_variance_is_one_seventy_fifth :
    (stationaryVariance (1/2) (1/10) : ℝ) = 1/75 := by
  rw [actual_stationary_variance_is_the_printed_nonnegative_real_variance
    (1/2) (1/10) (by norm_num) (by norm_num)]
  norm_num

theorem actual_literal_stationary_sd_is_the_sqrt_of_one_seventy_fifth :
    sourceStationarySD = Real.sqrt (1/75:ℝ) := by
  rw [sourceStationarySD, actual_literal_stationary_variance_is_one_seventy_fifth]

theorem actual_literal_stationary_sd_strict_decimal_enclosure :
    (115470/1000000:ℝ) < sourceStationarySD ∧
      sourceStationarySD < (115471/1000000:ℝ) := by
  rw [actual_literal_stationary_sd_is_the_sqrt_of_one_seventy_fifth]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/75)
  have hn := Real.sqrt_nonneg (1/75:ℝ)
  constructor <;> nlinarith

theorem actual_literal_stationary_sd_rounds_to_the_printed_four_decimals :
    |sourceStationarySD-(1155/10000:ℝ)| < 1/20000 := by
  obtain ⟨hl,hu⟩ := actual_literal_stationary_sd_strict_decimal_enclosure
  rw [abs_lt]
  constructor <;> linarith

theorem actual_literal_stationary_standardized_radius_is_sqrt_three :
    sourceStationaryZ = Real.sqrt 3 := by
  rw [sourceStationaryZ, actual_literal_stationary_sd_is_the_sqrt_of_one_seventy_fifth]
  norm_num only [show (1-4/5:ℝ) = 1/5 by norm_num]
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num : (0:ℝ) ≤ 3) (by positivity)).mpr
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/75)]
  norm_num

theorem actual_sqrt_three_strict_decimal_enclosure :
    (173205/100000:ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (173206/100000:ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  constructor <;> nlinarith

theorem actual_literal_stationary_radius_rounds_to_the_printed_three_decimals :
    |sourceStationaryZ-(1732/1000:ℝ)| < 1/2000 := by
  rw [actual_literal_stationary_standardized_radius_is_sqrt_three]
  obtain ⟨hl,hu⟩ := actual_sqrt_three_strict_decimal_enclosure
  rw [abs_lt]
  constructor <;> linarith

theorem actual_literal_stationary_violation_probability_is_the_true_standard_cdf_tail :
    sourceStationaryTail = 1-standardCDF (Real.sqrt 3) := by
  let v := stationaryVariance (1/2) (1/10)
  let sd := NNReal.sqrt v
  have hv : 0 < v := by
    rw [← NNReal.coe_pos]
    change (0:ℝ) < (stationaryVariance (1/2) (1/10) : ℝ)
    rw [actual_literal_stationary_variance_is_one_seventy_fifth]
    norm_num
  have hs : sd ≠ 0 := ne_of_gt (NNReal.sqrt_pos_of_pos hv)
  have hlaw : HasLaw (fun x : ℝ => x) (gaussianReal (4/5) (sd^2))
      (stationaryLaw (1/2) (4/5) (1/10)) := by
    refine ⟨measurable_id.aemeasurable, ?_⟩
    dsimp only [sd]
    rw [NNReal.sq_sqrt]
    exact Measure.map_id
  have h := actual_gaussian_upper_tail_is_the_standard_cdf_complement
    (stationaryLaw (1/2) (4/5) (1/10)) (fun x : ℝ => x) (4/5) 1 sd hs hlaw
  change sourceStationaryTail = 1-standardCDF ((1-4/5)/(sd : ℝ)) at h
  have he : (sd : ℝ) = sourceStationarySD := by
    simp only [sd, v, Real.coe_sqrt, sourceStationarySD]
  rw [he, ← sourceStationaryZ, actual_literal_stationary_standardized_radius_is_sqrt_three] at h
  exact h

theorem actual_true_stationary_tail_strict_probability_enclosure :
    (41631/1000000:ℝ) < 1-standardCDF (Real.sqrt 3) ∧
      1-standardCDF (Real.sqrt 3) < (41633/1000000:ℝ) := by
  have hpa : (1148957361251/1000000000000:ℝ) <
      actualTailPolynomialIntegral (173205/100000:ℝ) ∧
      actualTailPolynomialIntegral (173205/100000:ℝ) < (1148957361252/1000000000000:ℝ) := by
    norm_num [actualTailPolynomialIntegral, Finset.sum_range_succ, Nat.factorial]
  have hpb : (1148959592536/1000000000000:ℝ) <
      actualTailPolynomialIntegral (173206/100000:ℝ) ∧
      actualTailPolynomialIntegral (173206/100000:ℝ) < (1148959592537/1000000000000:ℝ) := by
    norm_num [actualTailPolynomialIntegral, Finset.sum_range_succ, Nat.factorial]
  have ha := actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
    (173205/100000:ℝ) (41631/1000000:ℝ) (41633/1000000:ℝ)
    (by constructor <;> norm_num) (by linarith [hpa.1])
    (by linarith [hpa.2]) (by linarith [hpa.1])
  have hb := actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
    (173206/100000:ℝ) (41631/1000000:ℝ) (41633/1000000:ℝ)
    (by constructor <;> norm_num) (by linarith [hpb.1])
    (by linarith [hpb.2]) (by linarith [hpb.1])
  exact actual_standardized_tail_inherits_both_true_endpoint_probability_bounds
    (Real.sqrt 3) (173205/100000) (173206/100000) (41631/1000000) (41633/1000000)
    ⟨actual_sqrt_three_strict_decimal_enclosure.1.le,
      actual_sqrt_three_strict_decimal_enclosure.2.le⟩ hb.1 ha.2

theorem actual_stationary_tail_rounds_to_the_printed_four_decimals :
    |sourceStationaryTail-(416/10000:ℝ)| < 1/20000 := by
  rw [actual_literal_stationary_violation_probability_is_the_true_standard_cdf_tail]
  obtain ⟨hl,hu⟩ := actual_true_stationary_tail_strict_probability_enclosure
  rw [abs_lt]
  constructor <;> linarith

theorem actual_stationary_forty_step_approximation_rounds_to_the_printed_three_decimals :
    |40*sourceStationaryTail-(1665/1000:ℝ)| < 1/2000 := by
  rw [actual_literal_stationary_violation_probability_is_the_true_standard_cdf_tail]
  obtain ⟨hl,hu⟩ := actual_true_stationary_tail_strict_probability_enclosure
  rw [abs_lt]
  constructor <;> linarith

theorem actual_stationary_decimals_are_approximations_and_all_printed_exact_equalities_fail :
    sourceStationarySD ≠ (1155/10000:ℝ) ∧ sourceStationaryZ ≠ (1732/1000:ℝ) ∧
      sourceStationaryTail ≠ (416/10000:ℝ) ∧ 40*sourceStationaryTail ≠ (1665/1000:ℝ) := by
  obtain ⟨hsl,hsu⟩ := actual_literal_stationary_sd_strict_decimal_enclosure
  have hz := actual_sqrt_three_strict_decimal_enclosure.1
  rw [← actual_literal_stationary_standardized_radius_is_sqrt_three] at hz
  have ht := actual_true_stationary_tail_strict_probability_enclosure.1
  rw [← actual_literal_stationary_violation_probability_is_the_true_standard_cdf_tail] at ht
  refine ⟨ne_of_lt (by linarith), ne_of_gt (by linarith),
    ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

end SafeLearning.CompleteModulesLandscapeARStationaryNumerics
