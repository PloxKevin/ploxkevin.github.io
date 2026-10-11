import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedGaussianNinetyQuantile
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianQuantile

theorem actual_point_ninety_gaussian_quantile_certified_cdf_bracket :
    standardCDF (128155156/100000000:ℝ)<9/10 ∧
    9/10<standardCDF (128155158/100000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_integral_uniform_rational_error
    (128155156/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_integral_uniform_rational_error
    (128155158/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (100265130741/100000000000:ℝ)<actualPolynomialIntegral
      (128155156/100000000:ℝ) ∧ actualPolynomialIntegral
      (128155156/100000000:ℝ)<100265130742/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (100265131621/100000000000:ℝ)<actualPolynomialIntegral
      (128155158/100000000:ℝ) ∧ actualPolynomialIntegral
      (128155158/100000000:ℝ)<100265131622/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

def truePointNinetyQuantile : ℝ := sInf {point : ℝ | (9/10:ℝ)≤ standardCDF point}

theorem actual_point_ninety_quantile_is_the_unique_cdf_root_and_smallest_threshold :
    standardCDF truePointNinetyQuantile=9/10 ∧
    (∀point:ℝ,(9/10:ℝ)≤ standardCDF point ↔ truePointNinetyQuantile≤point) ∧
    (128155156/100000000:ℝ)<truePointNinetyQuantile ∧
    truePointNinetyQuantile<(128155158/100000000:ℝ) := by
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hb := actual_point_ninety_gaussian_quantile_certified_cdf_bracket
  obtain ⟨root,hrange,hroot⟩ := intermediate_value_Icc
    (by norm_num : (128155156/100000000:ℝ)≤128155158/100000000)
    hc.1.continuousOn ⟨hb.1.le,hb.2.le⟩
  have hset : {point : ℝ | (9/10:ℝ)≤ standardCDF point}=Ici root := by
    ext point
    simp only [mem_setOf_eq,mem_Ici]
    rw [←hroot,hc.2.le_iff_le]
  have hq : truePointNinetyQuantile=root := by
    rw [truePointNinetyQuantile,hset,csInf_Ici]
  rw [hq]
  refine ⟨hroot,?_,?_,?_⟩
  · intro point;rw [←hroot,hc.2.le_iff_le]
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.1)
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.2)

end SafeLearning.CompleteAppliedGaussianNinetyQuantile
