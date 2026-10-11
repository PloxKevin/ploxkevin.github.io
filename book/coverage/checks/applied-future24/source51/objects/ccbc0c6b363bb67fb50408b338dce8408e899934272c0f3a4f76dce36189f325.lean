import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPConfidenceComparison
open CompleteModulesGPNumerics

def sourceSrinivasBeta : ℝ := 8+3000*(Real.log 2000)^3
def sourceSrinivasMultiplier : ℝ := Real.sqrt sourceSrinivasBeta
def sourceChowdhuryMultiplier : ℝ := 2+(1/10)*Real.sqrt (2*(11+Real.log 20))
def sourceMultiplierRatio : ℝ := sourceSrinivasMultiplier/sourceChowdhuryMultiplier

theorem actual_source_norm_conventions_and_regularizers :
    (2:ℝ)^2=4 ∧ 2*4=8 ∧ (1/10:ℝ)^2=1/100 ∧
      (1:ℝ)+2/100=51/50 ∧ (1/100:ℝ)<51/50 := by norm_num

theorem actual_source_formula_substitutions :
    2*(2:ℝ)^2+300*10*(Real.log ((100:ℝ)/(1/20)))^3= sourceSrinivasBeta ∧
      2+(1/10:ℝ)*Real.sqrt (2*(10+1+Real.log (1/(1/20:ℝ))))= sourceChowdhuryMultiplier := by
  norm_num [sourceSrinivasBeta,sourceChowdhuryMultiplier]

theorem actual_source_log_two_thousand_has_rigorous_bounds :
    (760090245/100000000:ℝ)< Real.log 2000 ∧
      Real.log 2000<(760090247/100000000:ℝ) := by
  have he : Real.log (2000:ℝ)= Real.log 20+2*(Real.log 2+Real.log 5) := by
    rw [show (2000:ℝ)=20*(2*5)^2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [he]
  constructor <;> linarith [log_twenty_enclosure.1,log_twenty_enclosure.2,
    Real.log_two_gt_d9,Real.log_two_lt_d9,Real.log_five_gt_d9,Real.log_five_lt_d9]

theorem actual_source_log_cube_and_beta_have_the_printed_roundings :
    |Real.log 2000-(76/10:ℝ)|<1/200 ∧
      |(Real.log 2000)^3-(439:ℝ)|<1/2 ∧
      |sourceSrinivasBeta-(1320000:ℝ)|<5000 := by
  have hl := actual_source_log_two_thousand_has_rigorous_bounds
  have hn : 0≤ Real.log (2000:ℝ) := by linarith [hl.1]
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤76009/10000)
    (show (76009/10000:ℝ)≤ Real.log 2000 by linarith [hl.1]) 3
  have hhi := pow_le_pow_left₀ hn
    (show Real.log (2000:ℝ)≤760091/100000 by linarith [hl.2]) 3
  norm_num at hlo hhi
  refine ⟨?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith [hl.1,hl.2]
  · rw [abs_lt];constructor <;> linarith
  · unfold sourceSrinivasBeta
    rw [abs_lt];constructor <;> linarith

theorem actual_source_srinivas_multiplier_is_positive_and_rounds_to_eleven_fifty :
    (1147:ℝ)< sourceSrinivasMultiplier ∧ sourceSrinivasMultiplier<1148 ∧
      |sourceSrinivasMultiplier-(1150:ℝ)|<5 := by
  have hl := actual_source_log_two_thousand_has_rigorous_bounds
  have hn : 0≤ Real.log (2000:ℝ) := by linarith [hl.1]
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤76009/10000)
    (show (76009/10000:ℝ)≤ Real.log 2000 by linarith [hl.1]) 3
  have hhi := pow_le_pow_left₀ hn
    (show Real.log (2000:ℝ)≤760091/100000 by linarith [hl.2]) 3
  have hbeta : 0≤ sourceSrinivasBeta := by unfold sourceSrinivasBeta;positivity
  have hs := Real.sq_sqrt hbeta
  have hp := Real.sqrt_nonneg sourceSrinivasBeta
  norm_num at hlo hhi
  unfold sourceSrinivasBeta at hs hp
  have ha : (1147:ℝ)< sourceSrinivasMultiplier := by
    unfold sourceSrinivasMultiplier sourceSrinivasBeta
    nlinarith
  have hb : sourceSrinivasMultiplier<(1148:ℝ) := by
    unfold sourceSrinivasMultiplier sourceSrinivasBeta
    nlinarith
  refine ⟨ha,hb,?_⟩
  rw [abs_lt];constructor <;> linarith

theorem actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings :
    (2529/1000:ℝ)< sourceChowdhuryMultiplier ∧ sourceChowdhuryMultiplier<253/100 ∧
      |sourceChowdhuryMultiplier-(253/100:ℝ)|<1/200 ∧
      |(sourceChowdhuryMultiplier-2)-(53/100:ℝ)|<1/200 := by
  have hl := log_twenty_enclosure
  have harg : 0≤2*(11+Real.log 20) := by linarith [hl.1]
  have hs := Real.sq_sqrt harg
  have hp := Real.sqrt_nonneg (2*(11+Real.log 20))
  have ha : (2529/1000:ℝ)< sourceChowdhuryMultiplier := by
    unfold sourceChowdhuryMultiplier
    nlinarith [hl.1]
  have hb : sourceChowdhuryMultiplier<(253/100:ℝ) := by
    unfold sourceChowdhuryMultiplier
    nlinarith [hl.2]
  refine ⟨ha,hb,?_,?_⟩
  all_goals rw [abs_lt];constructor <;> linarith

theorem actual_source_multiplier_ratio_is_positive_and_rounds_to_four_fifty :
    (453:ℝ)< sourceMultiplierRatio ∧ sourceMultiplierRatio<455 ∧
      |sourceMultiplierRatio-(450:ℝ)|<5 := by
  have hs := actual_source_srinivas_multiplier_is_positive_and_rounds_to_eleven_fifty
  have hc := actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings
  have hp : 0< sourceChowdhuryMultiplier := by linarith [hc.1]
  have ha : (453:ℝ)< sourceMultiplierRatio := by
    unfold sourceMultiplierRatio
    rw [lt_div_iff₀ hp]
    nlinarith [hs.1,hc.2.1]
  have hb : sourceMultiplierRatio<(455:ℝ) := by
    unfold sourceMultiplierRatio
    rw [div_lt_iff₀ hp]
    nlinarith [hs.2.1,hc.1]
  refine ⟨ha,hb,?_⟩
  rw [abs_lt];constructor <;> linarith

theorem actual_ordered_posterior_variances_bound_the_true_width_ratio
    (smallVariance largeVariance : ℝ) (hsmall : 0≤ smallVariance)
    (hlarge : 0< largeVariance) (horder : smallVariance≤ largeVariance) :
    (sourceSrinivasMultiplier*Real.sqrt smallVariance)/
      (sourceChowdhuryMultiplier*Real.sqrt largeVariance)≤ sourceMultiplierRatio := by
  have hs := actual_source_srinivas_multiplier_is_positive_and_rounds_to_eleven_fifty
  have hc := actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings
  have hcp : 0< sourceChowdhuryMultiplier := by linarith [hc.1]
  have hlp : 0< Real.sqrt largeVariance := Real.sqrt_pos.2 hlarge
  have hr : Real.sqrt smallVariance≤ Real.sqrt largeVariance := Real.sqrt_le_sqrt horder
  unfold sourceMultiplierRatio
  apply (div_le_div_iff₀ (mul_pos hcp hlp) hcp).mpr
  have hsp : 0 ≤ sourceSrinivasMultiplier := by linarith [hs.1]
  have hb := mul_le_mul_of_nonneg_left hr (mul_nonneg hsp hcp.le)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hb

def observedVariance (lambda : ℝ) : ℝ := 1-1/(1+lambda)
def observedWidthRatio : ℝ :=
  sourceSrinivasMultiplier*Real.sqrt (observedVariance (1/100))/
    (sourceChowdhuryMultiplier*Real.sqrt (observedVariance (51/50)))

theorem actual_single_observed_variance_formula_and_both_source_values
    (lambda : ℝ) (hlambda : 0< lambda) :
    observedVariance lambda= lambda/(1+lambda) ∧
      observedVariance (1/100)=1/101 ∧ observedVariance (51/50)=51/101 := by
  constructor
  · unfold observedVariance
    field_simp
    ring
  · norm_num [observedVariance]

theorem actual_observed_point_width_ratio_is_much_smaller_than_the_multiplier_ratio :
    (63:ℝ)< observedWidthRatio ∧ observedWidthRatio<64 ∧
      observedWidthRatio< sourceMultiplierRatio := by
  have hs := actual_source_srinivas_multiplier_is_positive_and_rounds_to_eleven_fifty
  have hc := actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings
  have hcp : 0< sourceChowdhuryMultiplier := by linarith [hc.1]
  have ha : (995/10000:ℝ)< Real.sqrt (1/101) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/101),Real.sqrt_nonneg (1/101)]
  have hb : Real.sqrt (1/101)<(996/10000:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/101),Real.sqrt_nonneg (1/101)]
  have hd : (710/1000:ℝ)< Real.sqrt (51/101) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤51/101),Real.sqrt_nonneg (51/101)]
  have he : Real.sqrt (51/101)<(711/1000:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤51/101),Real.sqrt_nonneg (51/101)]
  have hp : 0< sourceChowdhuryMultiplier*Real.sqrt (51/101) := by positivity
  have hv : observedWidthRatio= sourceSrinivasMultiplier*Real.sqrt (1/101)/
      (sourceChowdhuryMultiplier*Real.sqrt (51/101)) := by
    norm_num [observedWidthRatio,observedVariance]
  have hlow : (63:ℝ)< observedWidthRatio := by
    rw [hv,lt_div_iff₀ hp]
    nlinarith [hs.1,hc.2.1]
  have hhigh : observedWidthRatio<(64:ℝ) := by
    rw [hv,div_lt_iff₀ hp]
    nlinarith [hs.2.1,hc.1]
  exact ⟨hlow,hhigh,lt_trans hhigh (by linarith
    [actual_source_multiplier_ratio_is_positive_and_rounds_to_four_fifty.1])⟩

theorem actual_zero_cross_covariance_makes_the_width_ratio_equal_the_multiplier_ratio
    (priorVariance : ℝ) (hprior : 0< priorVariance) :
    sourceSrinivasMultiplier*Real.sqrt priorVariance/
      (sourceChowdhuryMultiplier*Real.sqrt priorVariance)= sourceMultiplierRatio := by
  have hs : Real.sqrt priorVariance≠0 := (Real.sqrt_pos.2 hprior).ne'
  unfold sourceMultiplierRatio
  field_simp

theorem actual_source_distinct_regularizers_are_not_the_same_posterior_parameter :
    (1/100:ℝ)≠51/50 := by norm_num

end SafeLearning.CompleteModulesGPConfidenceComparison
