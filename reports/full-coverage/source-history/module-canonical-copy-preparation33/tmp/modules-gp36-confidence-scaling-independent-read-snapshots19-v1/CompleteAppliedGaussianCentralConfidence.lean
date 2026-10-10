import SafeLearning.CompleteAppliedGaussianAlarmQuantile
import SafeLearning.CompleteAppliedGaussianChanceConstraint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix
namespace SafeLearning.CompleteAppliedGaussianCentralConfidence
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral
open CompleteAppliedGaussianQuantile CompleteAppliedGaussianAlarmQuantile

theorem actual_source_sum_direction_has_the_literal_mean_and_covariance_quadratic :
    (![1,1]:Fin 2→ℝ) ⬝ᵥ ![1,2]=3 ∧
      (![1,1]:Fin 2→ℝ) ⬝ᵥ ((![( ![1,1/2]),( ![1/2,4])]:Matrix (Fin 2) (Fin 2) ℝ)
        *ᵥ ![1,1])=6 := by
  norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_central_point_ninety_five_quantile_has_certified_cdf_enclosures :
    standardCDF (195996398/100000000:ℝ)<975/1000 ∧
      (975/1000:ℝ)<standardCDF (195996399/100000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_integral_uniform_rational_error
    (195996398/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_integral_uniform_rational_error
    (195996399/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (119064842978/100000000000:ℝ)<actualPolynomialIntegral
      (195996398/100000000:ℝ) ∧ actualPolynomialIntegral
      (195996398/100000000:ℝ)<119064842979/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (119064843124/100000000000:ℝ)<actualPolynomialIntegral
      (195996399/100000000:ℝ) ∧ actualPolynomialIntegral
      (195996399/100000000:ℝ)<119064843125/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

def trueCentralNinetyFiveRadius : ℝ := sInf {radius : ℝ | (975/1000:ℝ)≤ standardCDF radius}

theorem actual_central_quantile_is_the_unique_root_and_has_the_certified_bracket :
    standardCDF trueCentralNinetyFiveRadius=975/1000 ∧
    (∀radius:ℝ,(975/1000:ℝ)≤ standardCDF radius ↔ trueCentralNinetyFiveRadius≤radius) ∧
    (195996398/100000000:ℝ)<trueCentralNinetyFiveRadius ∧
    trueCentralNinetyFiveRadius<(195996399/100000000:ℝ) := by
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hb := actual_central_point_ninety_five_quantile_has_certified_cdf_enclosures
  obtain ⟨root,hrange,hroot⟩ := intermediate_value_Icc
    (by norm_num : (195996398/100000000:ℝ)≤195996399/100000000)
    hc.1.continuousOn ⟨hb.1.le,hb.2.le⟩
  have hset : {radius : ℝ | (975/1000:ℝ)≤ standardCDF radius}=Ici root := by
    ext radius
    simp only [mem_setOf_eq,mem_Ici]
    rw [←hroot,hc.2.le_iff_le]
  have hq : trueCentralNinetyFiveRadius=root := by
    rw [trueCentralNinetyFiveRadius,hset,csInf_Ici]
  rw [hq]
  refine ⟨hroot,?_,?_,?_⟩
  · intro radius;rw [←hroot,hc.2.le_iff_le]
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.1)
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.2)

theorem actual_central_standard_gaussian_probability (radius : ℝ) (hradius : 0≤radius) :
    (gaussianReal 0 1).real {point:ℝ | |point|≤radius}=2*standardCDF radius-1 := by
  have hc := measureReal_compl (μ:=gaussianReal 0 1)
    (s:={point:ℝ | |point|≤radius}) (by measurability)
  have he : {point:ℝ | |point|≤radius}ᶜ={point:ℝ | radius< |point|} := by
    ext point;simp
  rw [he,actual_standard_gaussian_two_sided_tail_probability radius hradius] at hc
  have hu : (gaussianReal 0 1).real univ=1 := by simp
  rw [hu] at hc
  linarith

theorem actual_two_sided_ninety_five_probability_and_one_point_nine_six_rounding :
    (gaussianReal 0 1).real {point:ℝ | |point|≤trueCentralNinetyFiveRadius}=95/100 ∧
    |trueCentralNinetyFiveRadius-(196/100:ℝ)|<1/200 ∧
    trueCentralNinetyFiveRadius<(196/100:ℝ) ∧
    (95/100:ℝ)<(gaussianReal 0 1).real {point:ℝ | |point|≤196/100} := by
  have hq := actual_central_quantile_is_the_unique_root_and_has_the_certified_bracket
  have hp : 0≤trueCentralNinetyFiveRadius := by linarith [hq.2.2.1]
  have hless : trueCentralNinetyFiveRadius<(196/100:ℝ) := by linarith [hq.2.2.2]
  refine ⟨?_,?_,hless,?_⟩
  · rw [actual_central_standard_gaussian_probability _ hp,hq.1];norm_num
  · rw [abs_lt];constructor <;> linarith [hq.2.2.1,hq.2.2.2]
  · have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2 hless
    rw [hq.1] at hc
    rw [actual_central_standard_gaussian_probability _ (by norm_num)]
    linarith

end SafeLearning.CompleteAppliedGaussianCentralConfidence
