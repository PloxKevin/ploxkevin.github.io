import SafeLearning.CompleteAppliedGaussianGeneralIntegral
import SafeLearning.CompleteAppliedGaussianAlarmQuantile
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOGaussianNumerics
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral

theorem actual_standard_gaussian_cdf_two_has_a_rigorous_rational_enclosure :
    (9772497/10000000:ℝ)<standardCDF 2 ∧ standardCDF 2<(9772501/10000000:ℝ) := by
  have he := actual_gaussian_exponential_integral_uniform_rational_error 2 (by norm_num)
  have hp : (1196288013/1000000000:ℝ)<actualPolynomialIntegral 2 ∧
      actualPolynomialIntegral 2<(1196288014/1000000000:ℝ) := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hi := abs_le.mp he
  have hc := actual_standard_gaussian_normalization_rational_enclosure
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

def actualSingleExceedanceProbability : ℝ := (gaussianReal 0 1).real {x : ℝ | 2 < |x|}

theorem actual_single_exceedance_equals_the_literal_reflected_cdf_and_rounds_to_point0455 :
    actualSingleExceedanceProbability=2*standardCDF (-2) ∧
      |actualSingleExceedanceProbability-(455/10000:ℝ)|≤1/20000 ∧
      (454998/10000000:ℝ)<actualSingleExceedanceProbability ∧
      actualSingleExceedanceProbability<(455006/10000000:ℝ) := by
  have hc := actual_standard_gaussian_cdf_two_has_a_rigorous_rational_enclosure
  have he := CompleteAppliedGaussianAlarmQuantile.actual_standard_gaussian_two_sided_tail_probability 2 (by norm_num)
  have hs := CompleteAppliedGaussianStandardization.actual_standard_gaussian_cdf_reflection 2
  change actualSingleExceedanceProbability=2*(1-standardCDF 2) at he
  refine ⟨by linarith,?_,by linarith,by linarith⟩
  rw [abs_le]
  constructor <;> linarith

theorem actual_one_sided_probability_and_twenty_five_exceedance_probabilities_have_the_source_roundings :
    |standardCDF (-2)-(23/1000:ℝ)|≤1/2000 ∧
      |(1-(1-actualSingleExceedanceProbability)^25)-(69/100:ℝ)|≤1/200 ∧
      |(1-(1-(455/10000:ℝ))^25)-(69/100:ℝ)|≤1/200 ∧
      (1/2:ℝ)<1-(1-actualSingleExceedanceProbability)^25 := by
  have hp := actual_single_exceedance_equals_the_literal_reflected_cdf_and_rounds_to_point0455
  have hlo : (1-(455006/10000000:ℝ))^25 ≤ (1-actualSingleExceedanceProbability)^25 := by
    exact pow_le_pow_left₀ (by norm_num) (by linarith [hp.2.2.2]) 25
  have hhi : (1-actualSingleExceedanceProbability)^25 ≤ (1-(454998/10000000:ℝ))^25 := by
    exact pow_le_pow_left₀ (by linarith [hp.2.2.2]) (by linarith [hp.2.2.1]) 25
  have hrlo : (1-(455006/10000000:ℝ))^25>(305/1000:ℝ) := by norm_num
  have hrhi : (1-(454998/10000000:ℝ))^25<(315/1000:ℝ) := by norm_num
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_le];constructor <;> linarith [hp.1,hp.2.2.1,hp.2.2.2]
  · rw [abs_le];constructor <;> linarith
  · norm_num [abs_le]
  · linarith

theorem actual_log_five_thousand_has_the_required_unrounded_bounds :
    (8517193/1000000:ℝ)<Real.log 5000 ∧ Real.log 5000<(8517194/1000000:ℝ) := by
  have ht := CompleteModulesGPNumerics.log_twenty_enclosure
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have he : (5000:ℝ)=(20:ℝ)^4/(2:ℝ)^5 := by norm_num
  rw [he,Real.log_div (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
  constructor <;> norm_num at * <;> linarith

theorem actual_gaussian_horizon_multiplier_rounds_to_four_point_one_three :
    |Real.sqrt (2*Real.log 5000)-(413/100:ℝ)|≤1/200 ∧
      (0:ℝ)<Real.sqrt (2*Real.log 5000) := by
  have hl := actual_log_five_thousand_has_the_required_unrounded_bounds
  have hs := Real.sq_sqrt (show 0≤2*Real.log 5000 by linarith)
  have hn := Real.sqrt_nonneg (2*Real.log 5000)
  refine ⟨?_,?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · nlinarith

end SafeLearning.CompleteModulesLoSBOGaussianNumerics
