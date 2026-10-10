import SafeLearning.CompleteAppliedSequentialCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedCalibrationConstants

theorem actual_source_two_likelihood_quadratic_and_completion (offset : ℝ) :
    offset^2/4+(2-offset)^2+(-1-offset)^2/4=
      (3/2)*offset^2-(7/2)*offset+17/4 ∧
    offset^2/4+(2-offset)^2+(-1-offset)^2/4=
      (3/2)*(offset-7/6)^2+53/24 := by
  constructor <;> ring

theorem actual_source_precision_and_precision_weighted_data :
    (1/4:ℝ)+1+1/4=3/2 ∧ (0/4:ℝ)+2-1/4=7/4 ∧
      (7/4:ℝ)/(3/2)=7/6 ∧ (3/2:ℝ)⁻¹=2/3 := by norm_num

theorem actual_source_offset_and_predictive_standard_deviations_are_certified_roundings :
    |Real.sqrt (2/3:ℝ)-(8165/10000)|<1/20000 ∧
      |Real.sqrt (5/3:ℝ)-(12910/10000)|<1/20000 := by
  have ho := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
  have hp := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
  have hn := Real.sqrt_nonneg (2/3:ℝ)
  have hm := Real.sqrt_nonneg (5/3:ℝ)
  constructor <;> rw [abs_lt] <;> constructor <;> nlinarith

end SafeLearning.CompleteAppliedCalibrationConstants
