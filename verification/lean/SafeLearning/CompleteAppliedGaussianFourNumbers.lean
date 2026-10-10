import SafeLearning.CompleteAppliedGaussianFourSource
import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedGaussianFourNumbers
open CompleteAppliedGaussianFourSource CompleteAppliedGaussianCDF
open CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianStandardization

theorem actual_four_data_standard_deviation_and_standardized_threshold_brackets :
    (24253562/100000000:ℝ)<sourceSigma ∧ sourceSigma<(24253563/100000000:ℝ) ∧
      (143095/100000:ℝ)<sourceStandardMagnitude ∧
      sourceStandardMagnitude<(143097/100000:ℝ) := by
  have hs:=actual_source_posterior_moments_and_precision_addition.2.2.2.2.2.2
  have hlo : (24253562/100000000:ℝ)<sourceSigma := by nlinarith [hs.1,hs.2]
  have hhi : sourceSigma<(24253563/100000000:ℝ) := by nlinarith [hs.1,hs.2]
  refine ⟨hlo,hhi,?_,?_⟩
  · unfold sourceStandardMagnitude
    rw [lt_div_iff₀ (by positivity : 0<170*sourceSigma)]
    linarith
  · unfold sourceStandardMagnitude
    rw [div_lt_iff₀ (by positivity : 0<170*sourceSigma)]
    linarith

theorem actual_posterior_parameters_and_safety_lower_bound_have_the_printed_roundings :
    |(1/17:ℝ)-588/10000|<1/20000 ∧ |(72/85:ℝ)-847/1000|<1/2000 ∧
      |sourceSigma-2425/10000|<1/20000 ∧
      |-sourceStandardMagnitude-(-(1431/1000:ℝ))|<1/2000 ∧
      |sourceLower-362/1000|<1/2000 ∧ (3/10:ℝ)<sourceLower ∧
      (1/17:ℝ)≠588/10000 ∧ (72/85:ℝ)≠847/1000 ∧
      sourceSigma≠2425/10000 ∧ sourceLower≠362/1000 := by
  have hs:=actual_four_data_standard_deviation_and_standardized_threshold_brackets
  have hlo : (3619875/10000000:ℝ)<sourceLower := by unfold sourceLower;linarith [hs.2.1]
  have hhi : sourceLower<(3619876/10000000:ℝ) := by unfold sourceLower;linarith [hs.1]
  refine ⟨by norm_num,by norm_num,?_,?_,?_,by linarith,by norm_num,by norm_num,?_,?_⟩
  · rw [abs_lt];constructor <;>linarith [hs.1,hs.2.1]
  · rw [abs_lt];constructor <;>linarith [hs.2.2.1,hs.2.2.2]
  · rw [abs_lt];constructor <;>linarith
  · intro h;rw [h] at hs;norm_num at hs
  · exact ne_of_lt (lt_trans hhi (by norm_num))

theorem actual_gaussian_integral_bounds_at_the_two_standardization_brackets :
    (923776/1000000:ℝ)<standardCDF (143095/100000:ℝ) ∧
      standardCDF (143097/100000:ℝ)<923783/1000000 := by
  have hc:=actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha:=actual_gaussian_exponential_integral_uniform_rational_error
    (143095/100000:ℝ) (by constructor <;>norm_num)
  have hb:=actual_gaussian_exponential_integral_uniform_rational_error
    (143097/100000:ℝ) (by constructor <;>norm_num)
  have hpa : (10622532331/10000000000:ℝ)<actualPolynomialIntegral (143095/100000:ℝ) ∧
      actualPolynomialIntegral (143095/100000:ℝ)<10622532332/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (10622604175/10000000000:ℝ)<actualPolynomialIntegral (143097/100000:ℝ) ∧
      actualPolynomialIntegral (143097/100000:ℝ)<10622604176/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;>nlinarith

theorem actual_true_posterior_half_threshold_probability_has_the_point_zero_seven_six_rounding :
    (76217/1000000:ℝ)<sourcePosterior.real {latent:ℝ | latent<1/2} ∧
      sourcePosterior.real {latent:ℝ | latent<1/2}<(76224/1000000:ℝ) ∧
      |sourcePosterior.real {latent:ℝ | latent<1/2}-(76/1000:ℝ)|<1/2000 ∧
      sourcePosterior.real {latent:ℝ | latent<1/2}≠(76/1000:ℝ) := by
  rw [actual_posterior_half_threshold_and_lower_bound_failure_probabilities.1,
    actual_standard_gaussian_cdf_reflection]
  have hs:=actual_four_data_standard_deviation_and_standardized_threshold_brackets
  have hc:=actual_gaussian_integral_bounds_at_the_two_standardization_brackets
  have hm:=actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hl:=hm hs.2.2.1
  have hh:=hm hs.2.2.2
  refine ⟨by linarith,by linarith,?_,?_⟩
  · rw [abs_lt];constructor <;>linarith
  · exact ne_of_gt (by linarith)

theorem actual_standard_gaussian_two_sigma_lower_failure_has_the_point_zero_two_three_rounding :
    (227501/10000000:ℝ)<standardCDF (-2) ∧
      standardCDF (-2)<227502/10000000 ∧
      |standardCDF (-2)-(23/1000:ℝ)|<1/2000 ∧
      standardCDF (-2)≠(23/1000:ℝ) := by
  have hc:=actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he:=actual_gaussian_exponential_integral_uniform_rational_error
    (2:ℝ) (by constructor <;>norm_num)
  have hp : (11962880133/10000000000:ℝ)<actualPolynomialIntegral (2:ℝ) ∧
      actualPolynomialIntegral (2:ℝ)<11962880134/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have h2 : (9772498/10000000:ℝ)<standardCDF 2 ∧
      standardCDF 2<(9772499/10000000:ℝ) := by
    rw [abs_le] at he
    rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
    constructor <;>nlinarith
  rw [actual_standard_gaussian_cdf_reflection]
  refine ⟨by linarith,by linarith,?_,?_⟩
  · rw [abs_lt];constructor <;>linarith
  · exact ne_of_lt (by linarith)

theorem actual_source_two_sigma_certificate_and_true_failure_probability :
    (3/10:ℝ)<sourceLower ∧
      |sourcePosterior.real {latent:ℝ | latent<sourceLower}-(23/1000:ℝ)|<1/2000 ∧
      sourcePosterior.real {latent:ℝ | latent<sourceLower}<(23/1000:ℝ) := by
  rw [actual_posterior_half_threshold_and_lower_bound_failure_probabilities.2]
  have hb:=actual_posterior_parameters_and_safety_lower_bound_have_the_printed_roundings
  have hp:=actual_standard_gaussian_two_sigma_lower_failure_has_the_point_zero_two_three_rounding
  exact ⟨hb.2.2.2.2.2.1,hp.2.2.1,by linarith [hp.2.1]⟩

end SafeLearning.CompleteAppliedGaussianFourNumbers
