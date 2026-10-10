import SafeLearning.CompleteAppliedGaussianAlarmQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SafeLearning.CompleteAppliedGaussianAlarmImplementation
open CompleteAppliedGaussianAlarmQuantile

theorem actual_upward_rounded_alarm_radius_has_the_required_per_step_level :
    trueTwoSidedAlarmQuantile<(389060/100000:ℝ) ∧
    (gaussianReal 0 1).real {point:ℝ|(389060/100000:ℝ)< |point|}≤1/10000 := by
  have hq := actual_two_sided_alarm_quantile_is_the_unique_cdf_root_and_smallest_threshold
  refine ⟨hq.2.2.2,?_⟩
  exact (actual_true_alarm_quantile_gives_the_required_two_sided_false_alarm_level.2
    (389060/100000:ℝ) (by norm_num)).mpr hq.2.2.2.le

theorem actual_exact_and_conservative_implementations_are_distinct_from_the_unsafe_two_decimal_rounding :
    (gaussianReal 0 1).real {point:ℝ|trueTwoSidedAlarmQuantile< |point|}=1/10000 ∧
    (gaussianReal 0 1).real {point:ℝ|(389060/100000:ℝ)< |point|}≤1/10000 ∧
    (1/10000:ℝ)<(gaussianReal 0 1).real {point:ℝ|(389/100:ℝ)< |point|} := by
  exact ⟨actual_true_alarm_quantile_gives_the_required_two_sided_false_alarm_level.1,
    actual_upward_rounded_alarm_radius_has_the_required_per_step_level.2,
    actual_printed_three_point_eight_nine_is_rounded_but_violates_the_exact_required_level.2.2⟩

end SafeLearning.CompleteAppliedGaussianAlarmImplementation
