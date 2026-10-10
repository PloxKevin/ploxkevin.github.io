import SafeLearning.CompleteAppliedGaussianTailMoment
import SafeLearning.CompleteAppliedGaussianNinetyQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedGaussianCVaRNumbers
open CompleteAppliedGaussianTailMoment CompleteAppliedGaussianNinetyQuantile
open CompleteAppliedGaussianQuantile CompleteAppliedGaussianGeneralIntegral

def sourceTrueGaussianRisk : ℝ :=
  4/5+10*Real.sqrt (124/25)*standardPDF truePointNinetyQuantile

theorem actual_source_standard_gaussian_quantile_and_density_factor_roundings :
    |truePointNinetyQuantile-(12816/10000:ℝ)|<1/20000 ∧
    (17549/100000:ℝ)<standardPDF truePointNinetyQuantile ∧
    standardPDF truePointNinetyQuantile<(17550/100000:ℝ) ∧
    |10*standardPDF truePointNinetyQuantile-(1755/1000:ℝ)|<1/2000 := by
  have hq := actual_point_ninety_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (128155156/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (128155158/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (4399090840/10000000000:ℝ)<twentiethPolynomial (128155156/100000000:ℝ) ∧
    twentiethPolynomial (128155156/100000000:ℝ)<4399090841/10000000000 := by
    norm_num [twentiethPolynomial,Finset.sum_range_succ,Nat.factorial]
  have hpb : (4399090728/10000000000:ℝ)<twentiethPolynomial (128155158/100000000:ℝ) ∧
    twentiethPolynomial (128155158/100000000:ℝ)<4399090729/10000000000 := by
    norm_num [twentiethPolynomial,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  have hqpos : 0<truePointNinetyQuantile := by linarith [hq.2.2.1]
  have hlo : Real.exp (-(128155158/100000000:ℝ)^2/2)<Real.exp (-truePointNinetyQuantile^2/2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [hq.2.2.2]
  have hhi : Real.exp (-truePointNinetyQuantile^2/2)<Real.exp (-(128155156/100000000:ℝ)^2/2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [hq.2.2.1]
  have hel : (43990907279/100000000000:ℝ)<Real.exp (-truePointNinetyQuantile^2/2) := by linarith
  have heh : Real.exp (-truePointNinetyQuantile^2/2)<(43990908411/100000000000:ℝ) := by linarith
  have hp : (17549/100000:ℝ)<standardPDF truePointNinetyQuantile ∧
      standardPDF truePointNinetyQuantile<(17550/100000:ℝ) := by
    unfold standardPDF
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.1.le) (sub_nonneg.mpr hel.le)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) (sub_nonneg.mpr heh.le)]
  refine ⟨?_,hp.1,hp.2,?_⟩
  · rw [abs_lt]
    constructor <;> linarith [hq.2.2.1,hq.2.2.2]
  · rw [abs_lt]
    constructor <;> linarith [hp.1,hp.2]

theorem actual_rounded_quantile_input_gives_the_printed_three_decimal_density_factor :
    |10*standardPDF (12816/10000:ℝ)-(1755/1000:ℝ)|<1/2000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (12816/10000:ℝ) (by constructor <;> norm_num)
  have hp : (4398817755/10000000000:ℝ)<twentiethPolynomial (12816/10000:ℝ) ∧
    twentiethPolynomial (12816/10000:ℝ)<4398817756/10000000000 := by
    norm_num [twentiethPolynomial,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  have hl : (43988177549/100000000000:ℝ)<Real.exp (-(12816/10000:ℝ)^2/2) := by linarith
  have hh : Real.exp (-(12816/10000:ℝ)^2/2)<(43988177561/100000000000:ℝ) := by linarith
  have hd : (17548/100000:ℝ)<standardPDF (12816/10000:ℝ) ∧
      standardPDF (12816/10000:ℝ)<(17549/100000:ℝ) := by
    unfold standardPDF
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.1.le) (sub_nonneg.mpr hl.le)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) (sub_nonneg.mpr hh.le)]
  rw [abs_lt]
  constructor <;> linarith [hd.1,hd.2]

theorem actual_gaussian_CVaR_and_true_discrete_gap_roundings_and_budget_verdict :
    |sourceTrueGaussianRisk-(471/100:ℝ)|<1/200 ∧
    |((6:ℝ)-sourceTrueGaussianRisk)-(13/10:ℝ)|<1/20 ∧
    (4708/1000:ℝ)<sourceTrueGaussianRisk ∧ sourceTrueGaussianRisk<(4709/1000:ℝ) ∧
    sourceTrueGaussianRisk<(5:ℝ) ∧ sourceTrueGaussianRisk<(6:ℝ) := by
  have hphi := actual_source_standard_gaussian_quantile_and_density_factor_roundings
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤124/25)
  have hn := Real.sqrt_nonneg (124/25:ℝ)
  have hsl : (222710/100000:ℝ)<Real.sqrt (124/25) := by nlinarith
  have hsh : Real.sqrt (124/25)<(222711/100000:ℝ) := by nlinarith
  have hl : (4708/1000:ℝ)<sourceTrueGaussianRisk := by
    unfold sourceTrueGaussianRisk
    nlinarith [mul_nonneg (sub_nonneg.mpr hsl.le) (sub_nonneg.mpr hphi.2.1.le)]
  have hh : sourceTrueGaussianRisk<(4709/1000:ℝ) := by
    unfold sourceTrueGaussianRisk
    nlinarith [mul_nonneg (sub_nonneg.mpr hsh.le) (sub_nonneg.mpr hphi.2.2.1.le)]
  refine ⟨?_,?_,hl,hh,by linarith,by linarith⟩
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith

end SafeLearning.CompleteAppliedGaussianCVaRNumbers
