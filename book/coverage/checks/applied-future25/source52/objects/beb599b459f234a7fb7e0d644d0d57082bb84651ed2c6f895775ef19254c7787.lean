import SafeLearning.CompleteModulesGPConfidenceComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteModulesGPConfidenceComparisonConsequences
open CompleteModulesGPConfidenceComparison CompleteModulesGPNumerics

theorem actual_source_logarithmic_argument_rounds_to_thirteen_point_nine_nine_six :
    |(11 + Real.log 20) - (13996 / 1000 : ℝ)| < 1 / 2000 ∧
      11 + Real.log 20 < (13996 / 1000 : ℝ) ∧
      11 + Real.log 20 ≠ (13996 / 1000 : ℝ) := by
  have h := log_twenty_enclosure
  have hs : 11 + Real.log 20 < (13996 / 1000 : ℝ) := by linarith [h.2]
  refine ⟨?_, hs, hs.ne⟩
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

def queryVariance (cross lambda : ℝ) : ℝ := 1 - cross ^ 2 / (1 + lambda)

theorem actual_small_query_covariance_makes_each_source_variance_tend_to_the_prior :
    Tendsto (fun cross : ℝ => queryVariance cross (1 / 100)) (𝓝 0) (𝓝 1) ∧
      Tendsto (fun cross : ℝ => queryVariance cross (51 / 50)) (𝓝 0) (𝓝 1) := by
  have hc (lambda : ℝ) : Continuous (fun cross : ℝ => queryVariance cross lambda) := by
    exact continuous_const.sub ((continuous_id.pow 2).div_const (1 + lambda))
  constructor
  · simpa only [queryVariance, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
      (hc (1 / 100)).continuousAt.tendsto (x := 0)
  · simpa only [queryVariance, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
      (hc (51 / 50)).continuousAt.tendsto (x := 0)

theorem actual_small_query_covariance_makes_the_width_ratio_tend_to_the_multiplier_ratio :
    Tendsto (fun cross : ℝ =>
      sourceSrinivasMultiplier * Real.sqrt (queryVariance cross (1 / 100)) /
        (sourceChowdhuryMultiplier * Real.sqrt (queryVariance cross (51 / 50))))
      (𝓝 0) (𝓝 sourceMultiplierRatio) := by
  have hv := actual_small_query_covariance_makes_each_source_variance_tend_to_the_prior
  have hc : 0 < sourceChowdhuryMultiplier := by
    linarith [actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings.1]
  have hs := hv.1.sqrt.const_mul sourceSrinivasMultiplier
  have hl := hv.2.sqrt.const_mul sourceChowdhuryMultiplier
  have h := hs.div hl (by simpa using hc.ne')
  convert h using 1 <;> simp [sourceMultiplierRatio]

end SafeLearning.CompleteModulesGPConfidenceComparisonConsequences
