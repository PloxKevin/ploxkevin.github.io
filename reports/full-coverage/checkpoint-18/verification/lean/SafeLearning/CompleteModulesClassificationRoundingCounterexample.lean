import SafeLearning.CompleteModulesClassificationNumbers

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesClassificationRoundingCounterexample
open CompleteModulesClassificationNumbers

theorem actual_source_global_radius_squared : actualGlobalRadius^2=(81/200:ℝ) := by
  rw [actual_source_logit_margins_and_global_radius.2.2,div_pow,Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  norm_num

theorem actual_source_global_radius_is_not_printed_rounded_decimal :
    actualGlobalRadius≠(6364/10000:ℝ) := by
  intro he
  have hs := congrArg (fun value : ℝ => value^2) he
  rw [actual_source_global_radius_squared] at hs
  norm_num at hs

theorem actual_source_runnerup_ratio_is_not_printed_rounded_decimal :
    (68/27:ℝ)≠2519/1000 := by norm_num

theorem actual_source_small_perturbation_is_not_printed_rounded_decimal :
    (36/255:ℝ)≠1412/10000 := by norm_num

theorem actual_source_large_perturbation_is_not_printed_rounded_decimal :
    (72/255:ℝ)≠2824/10000 := by norm_num

theorem actual_source_normalized_global_radius_is_not_printed_rounded_decimal :
    actualGlobalRadius/4≠(159/1000:ℝ) := by
  intro he
  have hs := congrArg (fun value : ℝ => value^2) he
  rw [div_pow,actual_source_global_radius_squared] at hs
  norm_num at hs

end SafeLearning.CompleteModulesClassificationRoundingCounterexample
