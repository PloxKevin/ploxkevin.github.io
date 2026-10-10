import SafeLearning.CompleteAppliedGaussianCVaR
import SafeLearning.CompleteCMDPTailRisk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SafeLearning.CompleteCMDPGaussianTailRisk
open CompleteAppliedGaussianCVaR CompleteAppliedGaussianCDF
open CompleteAppliedGaussianQuantile CompleteAppliedGaussianTailMoment
open CompleteAppliedGaussianGeneralIntegral CompleteAppliedFractionalTailDual
open CompleteFoundationsCVaRQuotients

def sourceGaussianRisk : ℝ :=
  14/5+20*Real.sqrt (5004/25)*standardPDF truePointNinetyFiveQuantile

def lowerPointFiveQuantile : ℝ := sInf {point : ℝ | (1/20:ℝ) ≤ standardCDF point}

theorem actual_standard_CDF_reflection (point : ℝ) :
    standardCDF (-point)=1-standardCDF point := by
  let μ := gaussianReal 0 1
  haveI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
  have hm : μ.map (fun x : ℝ=>-x)=μ := by
    simpa [μ] using (gaussianReal_map_neg (μ:=0) (v:=1))
  have hp : (fun x : ℝ=>-x) ⁻¹' Iic (-point)=Ici point := by
    ext x;simp
  have hsym := map_measureReal_apply (μ:=μ)
    (by fun_prop : Measurable (fun x : ℝ=>-x)) (s:=Iic (-point)) measurableSet_Iic
  rw [hm,hp] at hsym
  have htotal := measureReal_union_add_inter (μ:=μ) (s:=Iic point) (t:=Ici point)
    measurableSet_Ici
  simp only [Iic_union_Ici,Iic_inter_Ici,Icc_self] at htotal
  have hu : μ.real univ=1 := by simp [μ]
  have hz : μ.real {point}=0 := by simp [measureReal_def]
  rw [hu,hz,add_zero] at htotal
  change μ.real (Iic (-point))=1-μ.real (Iic point)
  linarith

theorem actual_lower_quantile_and_density_symmetry :
    lowerPointFiveQuantile=-truePointNinetyFiveQuantile ∧
    standardCDF lowerPointFiveQuantile=1/20 ∧
    standardPDF lowerPointFiveQuantile=standardPDF truePointNinetyFiveQuantile := by
  have hq := actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hr : standardCDF (-truePointNinetyFiveQuantile)=1/20 := by
    rw [actual_standard_CDF_reflection,hq.1];norm_num
  have he : {point:ℝ | (1/20:ℝ) ≤ standardCDF point}=Ici (-truePointNinetyFiveQuantile) := by
    ext point
    simp only [Set.mem_setOf_eq,Set.mem_Ici,←hr,hc.2.le_iff_le]
  have hl : lowerPointFiveQuantile=-truePointNinetyFiveQuantile := by
    simp only [lowerPointFiveQuantile,he,csInf_Ici]
  refine ⟨hl,by rw [hl];exact hr,?_⟩
  rw [hl]
  simp [standardPDF]

theorem actual_two_moment_Gaussian_fit_and_true_tail_value :
    HasLaw (gaussianLoss (14/5) (Real.sqrt (5004/25)))
      (gaussianReal (14/5) (5004/25)) (gaussianReal 0 1) ∧
    actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (14/5) (Real.sqrt (5004/25))) (1/20)=sourceGaussianRisk ∧
    IsLeast (Set.range (actualRUObjective (gaussianReal 0 1)
      (gaussianLoss (14/5) (Real.sqrt (5004/25))) (19/20))) sourceGaussianRisk := by
  have hs : (Real.sqrt (5004/25:ℝ))^2=5004/25 := Real.sq_sqrt (by norm_num)
  have hl := actual_affine_standard_gaussian_loss_has_the_requested_gaussian_law (14/5) (Real.sqrt (5004/25))
  have hv : NNReal.mk ((Real.sqrt (5004/25:ℝ))^2) (sq_nonneg _)=(5004/25:NNReal) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk];exact hs
  rw [hv] at hl
  have hr := actual_gaussian_fractional_worst_tail_and_RU_minimum (14/5) (Real.sqrt (5004/25))
    (19/20) truePointNinetyFiveQuantile (by positivity) (by norm_num)
    (by convert actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold.1 using 1 <;> norm_num)
  have he : (1:ℝ)-19/20=1/20 := by norm_num
  rw [he] at hr
  have heq : (14/5:ℝ)+Real.sqrt (5004/25)*standardPDF truePointNinetyFiveQuantile/(1/20)=sourceGaussianRisk := by
    unfold sourceGaussianRisk;ring
  rw [heq] at hr
  exact ⟨hl,hr.2.2,hr.2.1⟩

theorem actual_source_lower_quantile_formula :
    sourceGaussianRisk=14/5+Real.sqrt (5004/25)*standardPDF lowerPointFiveQuantile/(1/20) := by
  rw [actual_lower_quantile_and_density_symmetry.2.2]
  unfold sourceGaussianRisk;ring

theorem actual_source_quantile_density_and_deviation_enclosures :
    |lowerPointFiveQuantile-(-1645/1000:ℝ)|<1/2000 ∧
    (1031356/10000000:ℝ)<standardPDF truePointNinetyFiveQuantile ∧
    standardPDF truePointNinetyFiveQuantile<(1031357/10000000:ℝ) ∧
    (1414779/100000:ℝ)<Real.sqrt (5004/25) ∧
    Real.sqrt (5004/25)<(1414780/100000:ℝ) := by
  have hq := actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (164485362/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (164485364/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (2585227152/10000000000:ℝ)<twentiethPolynomial (164485362/100000000:ℝ) ∧
    twentiethPolynomial (164485362/100000000:ℝ)<2585227153/10000000000 := by
    norm_num [twentiethPolynomial,Finset.sum_range_succ,Nat.factorial]
  have hpb : (2585227067/10000000000:ℝ)<twentiethPolynomial (164485364/100000000:ℝ) ∧
    twentiethPolynomial (164485364/100000000:ℝ)<2585227068/10000000000 := by
    norm_num [twentiethPolynomial,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  have hqpos : 0<truePointNinetyFiveQuantile := by linarith [hq.2.2.1]
  have hlo : Real.exp (-(164485364/100000000:ℝ)^2/2)<Real.exp (-truePointNinetyFiveQuantile^2/2) := by
    apply Real.exp_lt_exp.mpr;nlinarith [hq.2.2.2]
  have hhi : Real.exp (-truePointNinetyFiveQuantile^2/2)<Real.exp (-(164485362/100000000:ℝ)^2/2) := by
    apply Real.exp_lt_exp.mpr;nlinarith [hq.2.2.1]
  have hel : (25852270669/100000000000:ℝ)<Real.exp (-truePointNinetyFiveQuantile^2/2) := by linarith
  have heh : Real.exp (-truePointNinetyFiveQuantile^2/2)<(25852271531/100000000000:ℝ) := by linarith
  have hp : (1031356/10000000:ℝ)<standardPDF truePointNinetyFiveQuantile ∧
      standardPDF truePointNinetyFiveQuantile<(1031357/10000000:ℝ) := by
    unfold standardPDF
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.1.le) (sub_nonneg.mpr hel.le)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) (sub_nonneg.mpr heh.le)]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5004/25)
  have hn := Real.sqrt_nonneg (5004/25:ℝ)
  refine ⟨?_,hp.1,hp.2,by nlinarith,by nlinarith⟩
  rw [actual_lower_quantile_and_density_symmetry.1,abs_lt]
  constructor <;> linarith [hq.2.2.1,hq.2.2.2]

theorem actual_Gaussian_risk_and_discrete_underestimation_enclosures :
    (31982/1000:ℝ)<sourceGaussianRisk ∧ sourceGaussianRisk<(31984/1000:ℝ) ∧
    (30/100:ℝ)<(46-sourceGaussianRisk)/46 ∧
    (46-sourceGaussianRisk)/46<(31/100:ℝ) ∧
    sourceGaussianRisk<32 ∧ (32:ℝ)<46 := by
  have h := actual_source_quantile_density_and_deviation_enclosures
  have hl : (31982/1000:ℝ)<sourceGaussianRisk := by
    unfold sourceGaussianRisk
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.2.2.1.le) (sub_nonneg.mpr h.2.1.le)]
  have hh : sourceGaussianRisk<(31984/1000:ℝ) := by
    unfold sourceGaussianRisk
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.2.2.2.le) (sub_nonneg.mpr h.2.2.1.le)]
  refine ⟨hl,hh,?_,?_,by linarith,by norm_num⟩ <;> linarith

end SafeLearning.CompleteCMDPGaussianTailRisk
