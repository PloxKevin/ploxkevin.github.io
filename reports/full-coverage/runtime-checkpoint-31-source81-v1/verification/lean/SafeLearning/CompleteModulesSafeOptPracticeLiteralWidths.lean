import SafeLearning.CompleteModulesSafeOptPracticeNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SafeLearning.CompleteModulesSafeOptPracticeLiteralWidths
open SafeLearning.CompleteModulesSafeOptPracticeNumbers

theorem actual_source_two_maximizer_widths_and_their_strict_order :
    candidateUpper 0-candidateLower 0=(2/5:ℝ) ∧
      candidateUpper 1-candidateLower 1=(1/10:ℝ) ∧
      candidateUpper 1-candidateLower 1<candidateUpper 0-candidateLower 0 := by
  norm_num [candidateUpper,candidateLower]

theorem actual_source_point_one_lower_transfer_cannot_certify_point_two :
    expanderLower 1-expanderDistance 1 2=(-3/5:ℝ) ∧
      expanderLower 1-expanderDistance 1 2<0 := by norm_num [expanderLower,expanderDistance]

end SafeLearning.CompleteModulesSafeOptPracticeLiteralWidths
