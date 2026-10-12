import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesGPLinearInformationNumbers

theorem actual_three_halves_log_is_the_difference_of_trusted_logarithms :
    Real.log (3/2:ℝ)=Real.log 3-Real.log 2 := by
  exact Real.log_div (by norm_num) (by norm_num)

theorem actual_half_log_two_rounds_to_the_printed_three_decimal_value :
    |(1/2:ℝ)*Real.log 2-347/1000| < 1/2000 := by
  rw [abs_lt]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem actual_log_three_halves_rounds_to_the_printed_three_decimal_value :
    |Real.log (3/2:ℝ)-405/1000| < 1/2000 := by
  rw [actual_three_halves_log_is_the_difference_of_trusted_logarithms,abs_lt]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,
    Real.log_three_gt_d9,Real.log_three_lt_d9]

theorem actual_printed_single_sample_two_dimensional_information_gap_is_strict :
    (1/2:ℝ)*Real.log 2 < Real.log (3/2:ℝ) := by
  rw [actual_three_halves_log_is_the_difference_of_trusted_logarithms]
  linarith [Real.log_two_lt_d9,Real.log_three_gt_d9]

theorem actual_printed_single_sample_two_dimensional_bounds_have_the_logarithmic_values :
    (1:ℝ)/2*Real.log (1+1/1)=(1/2:ℝ)*Real.log 2 ∧
      (2:ℝ)/2*Real.log (1+1/(1*2))=Real.log (3/2:ℝ) := by
  constructor <;> norm_num

end SafeLearning.CompleteModulesGPLinearInformationNumbers
