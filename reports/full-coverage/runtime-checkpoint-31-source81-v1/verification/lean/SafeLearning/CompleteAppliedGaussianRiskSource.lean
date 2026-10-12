import SafeLearning.CompleteAppliedGaussianCVaR
import SafeLearning.CompleteAppliedGaussianCVaRNumbers
import SafeLearning.CompleteAppliedRiskPrimer

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteAppliedGaussianRiskSource
open CompleteAppliedGaussianCVaR CompleteAppliedGaussianCVaRNumbers CompleteAppliedGaussianNinetyQuantile
open CompleteAppliedGaussianTailMoment CompleteAppliedFractionalTailDual

/-- These are actual Gaussian moments of the law matched to the literal discrete distribution. -/
theorem actual_source_gaussian_mean_and_variance_match_the_true_discrete_moments :
    (∫point,gaussianLoss (4/5) (Real.sqrt (124/25)) point ∂gaussianReal 0 1)=4/5 ∧
    Var[gaussianLoss (4/5) (Real.sqrt (124/25));gaussianReal 0 1]=124/25 := by
  have hl := actual_source_matched_gaussian_has_true_mean_variance_law_and_CVaR.1
  constructor
  · rw [hl.integral_eq,integral_id_gaussianReal]
  · rw [hl.variance_eq,variance_id_gaussianReal]
    norm_num

theorem actual_source_gaussian_CVaR_is_the_genuine_RU_minimum_and_fractional_tail_supremum :
    IsLeast (Set.range (CompleteFoundationsCVaRQuotients.actualRUObjective (gaussianReal 0 1)
      (gaussianLoss (4/5) (Real.sqrt (124/25))) (9/10))) sourceTrueGaussianRisk ∧
    actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (4/5) (Real.sqrt (124/25))) (1/10)=sourceTrueGaussianRisk := by
  have hr := actual_gaussian_fractional_worst_tail_and_RU_minimum (4/5) (Real.sqrt (124/25))
    (9/10) truePointNinetyQuantile (by positivity) (by norm_num)
    actual_point_ninety_quantile_is_the_unique_cdf_root_and_smallest_threshold.1
  have hvalue : (4/5:ℝ)+Real.sqrt (124/25)*standardPDF truePointNinetyQuantile/((1:ℝ)-9/10)=sourceTrueGaussianRisk := by
    unfold sourceTrueGaussianRisk
    norm_num
    ring
  rw [hvalue] at hr
  have hm : (1:ℝ)-9/10=1/10 := by norm_num
  rw [hm] at hr
  exact ⟨hr.2.1,hr.2.2⟩

theorem actual_Gaussian_shortcut_accepts_a_budget_rejected_by_the_true_discrete_CVaR :
    actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (4/5) (Real.sqrt (124/25))) (1/10)<5 ∧
    CompleteAppliedTailRiskOptima.upperTailCVaR CompleteAppliedTailRisk.lossLaw CompleteAppliedRiskPrimer.sourceCost (9/10)>5 ∧
    |actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (4/5) (Real.sqrt (124/25))) (1/10)-(471/100:ℝ)|<1/200 ∧
    |((6:ℝ)-actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (4/5) (Real.sqrt (124/25))) (1/10))-(13/10:ℝ)|<1/20 := by
  rw [actual_source_gaussian_CVaR_is_the_genuine_RU_minimum_and_fractional_tail_supremum.2,
    CompleteAppliedRiskPrimer.actual_source_fractional_CVaR]
  have hn := actual_gaussian_CVaR_and_true_discrete_gap_roundings_and_budget_verdict
  exact ⟨hn.2.2.2.2.1,by norm_num,hn.1,hn.2.1⟩

end SafeLearning.CompleteAppliedGaussianRiskSource
