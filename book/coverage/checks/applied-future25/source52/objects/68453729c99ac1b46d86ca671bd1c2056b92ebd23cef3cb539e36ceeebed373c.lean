import SafeLearning.CompleteAppliedGaussianGeneralIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral

theorem actual_standard_gaussian_cdf_has_the_true_positive_density_derivative
    (point : ℝ) : HasDerivAt standardCDF
      ((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-point^2/2)) point := by
  have hc : Continuous (fun value : ℝ=>Real.exp (-value^2/2)) := by fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0:ℝ) point) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt
  have hf := (hd.const_mul (Real.sqrt (2*Real.pi))⁻¹).const_add (1/2:ℝ)
  convert hf using 1
  funext radius
  exact actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral radius

theorem actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing :
    Continuous standardCDF ∧ StrictMono standardCDF := by
  constructor
  · exact continuous_iff_continuousAt.mpr (fun point=>
      (actual_standard_gaussian_cdf_has_the_true_positive_density_derivative point).continuousAt)
  · exact strictMono_of_hasDerivAt_pos
      actual_standard_gaussian_cdf_has_the_true_positive_density_derivative
      (fun point=>by positivity)

theorem actual_standard_gaussian_normalization_high_precision_rational_enclosure :
    (398942280401/1000000000000:ℝ)<(Real.sqrt (2*Real.pi))⁻¹ ∧
    (Real.sqrt (2*Real.pi))⁻¹<(398942280402/1000000000000:ℝ) := by
  have hp := Real.pi_gt_d20
  have hq := Real.pi_lt_d20
  have hs : (Real.sqrt (2*Real.pi))^2=2*Real.pi := Real.sq_sqrt (by positivity)
  have hpos : 0<Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · rw [←one_div,lt_div_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (2*Real.pi)]
  · rw [←one_div,div_lt_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (2*Real.pi)]

theorem actual_point_ninety_five_gaussian_quantile_certified_cdf_bracket :
    standardCDF (164485362/100000000:ℝ)<95/100 ∧
    95/100<standardCDF (164485364/100000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_integral_uniform_rational_error
    (164485362/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_integral_uniform_rational_error
    (164485364/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (112798272178/100000000000:ℝ)<actualPolynomialIntegral
      (164485362/100000000:ℝ) ∧ actualPolynomialIntegral
      (164485362/100000000:ℝ)<112798272179/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (112798272695/100000000000:ℝ)<actualPolynomialIntegral
      (164485364/100000000:ℝ) ∧ actualPolynomialIntegral
      (164485364/100000000:ℝ)<112798272696/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

def truePointNinetyFiveQuantile : ℝ := sInf {point : ℝ | (95/100:ℝ)≤ standardCDF point}

theorem actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold :
    standardCDF truePointNinetyFiveQuantile=95/100 ∧
    (∀point:ℝ,(95/100:ℝ)≤ standardCDF point ↔ truePointNinetyFiveQuantile≤point) ∧
    (164485362/100000000:ℝ)<truePointNinetyFiveQuantile ∧
    truePointNinetyFiveQuantile<(164485364/100000000:ℝ) := by
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hb := actual_point_ninety_five_gaussian_quantile_certified_cdf_bracket
  obtain ⟨root,hrange,hroot⟩ := intermediate_value_Icc
    (by norm_num : (164485362/100000000:ℝ)≤164485364/100000000)
    hc.1.continuousOn ⟨hb.1.le,hb.2.le⟩
  have hset : {point : ℝ | (95/100:ℝ)≤ standardCDF point}=Ici root := by
    ext point
    simp only [mem_setOf_eq,mem_Ici]
    rw [←hroot,hc.2.le_iff_le]
  have hq : truePointNinetyFiveQuantile=root := by
    rw [truePointNinetyFiveQuantile,hset,csInf_Ici]
  rw [hq]
  refine ⟨hroot,?_,?_,?_⟩
  · intro point;rw [←hroot,hc.2.le_iff_le]
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.1)
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.2)

theorem actual_supplied_five_decimal_quantile_is_a_rounding_and_not_the_exact_root :
    |truePointNinetyFiveQuantile-(164485/100000:ℝ)|<1/200000 ∧
      (164485/100000:ℝ)<truePointNinetyFiveQuantile ∧
      standardCDF (164485/100000:ℝ)<95/100 := by
  have hr := actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hless : (164485/100000:ℝ)<truePointNinetyFiveQuantile := by linarith [hr.2.2.1]
  refine ⟨?_,hless,?_⟩
  · rw [abs_lt];constructor <;> linarith [hr.2.2.1,hr.2.2.2]
  · rw [←hr.1];exact hc.2 hless

end SafeLearning.CompleteAppliedGaussianQuantile
