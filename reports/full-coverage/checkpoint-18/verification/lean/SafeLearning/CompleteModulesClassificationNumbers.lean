import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesClassificationNumbers

def actualSourceLogits : Fin 3 → ℝ := ![4,31/10,3/5]
def actualGlobalRadius : ℝ := min (actualSourceLogits 0-actualSourceLogits 1)
    (actualSourceLogits 0-actualSourceLogits 2)/Real.sqrt 2

def actualPairwiseRadius : ℝ := min ((actualSourceLogits 0-actualSourceLogits 1)/(6/5))
    ((actualSourceLogits 0-actualSourceLogits 2)/(27/20))

theorem actual_source_class_one_is_unique_maximum :
    ∀ other : Fin 3,other≠0 → actualSourceLogits other < actualSourceLogits 0 := by
  intro other hother
  fin_cases other <;> norm_num [actualSourceLogits] at *

theorem actual_source_logit_margins_and_global_radius :
    actualSourceLogits 0-actualSourceLogits 1=(9/10:ℝ) ∧
    actualSourceLogits 0-actualSourceLogits 2=(17/5:ℝ) ∧
    actualGlobalRadius=(9/10:ℝ)/Real.sqrt 2 := by
  norm_num [actualGlobalRadius,actualSourceLogits]

theorem actual_source_pairwise_radius_and_runnerup_ratio :
    actualPairwiseRadius=(3/4:ℝ) ∧
    (actualSourceLogits 0-actualSourceLogits 2)/(27/20)=(68/27:ℝ) := by
  norm_num [actualPairwiseRadius,actualSourceLogits]

theorem actual_source_global_radius_decimal_error :
    |actualGlobalRadius-(6364/10000:ℝ)| < 1/20000 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  have he : (9/10:ℝ)/Real.sqrt 2=9*Real.sqrt 2/20 := by field_simp; nlinarith
  rw [actual_source_logit_margins_and_global_radius.2.2,he,abs_lt]
  constructor <;> nlinarith

theorem actual_source_runnerup_ratio_decimal_error :
    |(68/27:ℝ)-(2519/1000:ℝ)| < 1/2000 := by norm_num

theorem actual_source_pairwise_radius_relative_improvement_about_eighteen_percent :
    |(actualPairwiseRadius/actualGlobalRadius-1)-(18/100:ℝ)| < 1/200 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  rw [actual_source_pairwise_radius_and_runnerup_ratio.1,
    actual_source_logit_margins_and_global_radius.2.2]
  have he : (3/4:ℝ)/((9/10)/Real.sqrt 2)-1=5*Real.sqrt 2/6-1 := by field_simp;ring
  rw [he,abs_lt]
  constructor <;> nlinarith

theorem actual_source_pixel_perturbation_decimal_errors :
    |(36/255:ℝ)-(1412/10000:ℝ)| < 1/20000 ∧
    |(72/255:ℝ)-(2824/10000:ℝ)| < 1/20000 := by norm_num

theorem actual_source_both_unnormalized_radii_exceed_both_perturbation_levels :
    (36/255:ℝ) < actualGlobalRadius ∧ (72/255:ℝ) < actualGlobalRadius ∧
    (36/255:ℝ) < actualPairwiseRadius ∧ (72/255:ℝ) < actualPairwiseRadius := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  rw [actual_source_logit_margins_and_global_radius.2.2,
    actual_source_pairwise_radius_and_runnerup_ratio.1]
  constructor
  · rw [lt_div_iff₀ hp]
    nlinarith
  · constructor
    · rw [lt_div_iff₀ hp]
      nlinarith
    · norm_num

theorem actual_source_normalized_pixel_radii_and_decimal_bound :
    actualPairwiseRadius/4=(3/16:ℝ) ∧
    |actualGlobalRadius/4-(159/1000:ℝ)| < 1/2000 := by
  rw [actual_source_pairwise_radius_and_runnerup_ratio.1]
  constructor
  · norm_num
  · have hs := actual_source_global_radius_decimal_error
    rw [abs_lt] at *
    constructor <;> linarith [hs.1,hs.2]

theorem actual_source_normalized_pixel_radii_certify_only_smaller_level :
    (36/255:ℝ) < actualGlobalRadius/4 ∧ actualGlobalRadius/4 < (72/255:ℝ) ∧
    (36/255:ℝ) < actualPairwiseRadius/4 ∧ actualPairwiseRadius/4 < (72/255:ℝ) := by
  have hs := actual_source_global_radius_decimal_error
  rw [abs_lt] at hs
  rw [actual_source_pairwise_radius_and_runnerup_ratio.1]
  constructor
  · linarith [hs.1]
  · constructor
    · linarith [hs.2]
    · norm_num

end SafeLearning.CompleteModulesClassificationNumbers
