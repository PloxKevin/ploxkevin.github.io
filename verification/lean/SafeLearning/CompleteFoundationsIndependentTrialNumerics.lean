import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1200
noncomputable section

namespace SafeLearning.CompleteFoundationsIndependentTrialNumerics

theorem actual_three_hundred_trial_miss_probability_rounds_to_four_decimals :
    |(99 / 100 : ℝ) ^ 300 - 490 / 10000| < 1 / 20000 := by
  norm_num [abs_lt]

theorem actual_three_hundred_trial_miss_probability_is_strictly_above_its_printed_rounding :
    490 / 10000 < (99 / 100 : ℝ) ^ 300 ∧
      (99 / 100 : ℝ) ^ 300 ≠ 490 / 10000 := by
  constructor <;> norm_num

end SafeLearning.CompleteFoundationsIndependentTrialNumerics
