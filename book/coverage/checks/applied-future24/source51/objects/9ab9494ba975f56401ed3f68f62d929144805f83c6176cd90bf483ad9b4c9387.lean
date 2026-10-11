import SafeLearning.CompleteModulesSafeOptEightPointReachability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptEightPointRadii
open SafeLearning.CompleteModulesSafeOptEightPointReachability

theorem actual_certificate_is_exactly_the_anchor_radius_test
    (epsilon : ℝ) (anchor candidate : Fin 8) :
    0 ≤ actualValue anchor-epsilon-actualDistance anchor candidate ↔
      actualDistance anchor candidate ≤ actualValue anchor-epsilon := by
  constructor <;> intro h <;> linarith

theorem actual_printed_slack_point_two_anchor_radii_and_zero_slack_gap :
    actualValue 2-(1/5:ℝ)=9/5 ∧ actualValue 1-(1/5:ℝ)=1 ∧
      actualValue 3-(1/5:ℝ)=6/5 ∧ actualValue 0-(1/5:ℝ)=3/10 ∧
      actualValue 4-(1/5:ℝ)=1/5 ∧ actualValue 4=(2/5:ℝ) ∧
      actualValue 4 < actualDistance 4 5 ∧
      (∀ anchor : Fin 8, actualValue anchor-0=(actualValue anchor-(1/5:ℝ))+1/5) := by
  norm_num [actualValue,actualDistance]

theorem actual_source_individual_anchor_certified_sets_are_the_printed_three_point_sets :
    {candidate | 0 ≤ actualValue 1-(1/5:ℝ)-actualDistance 1 candidate}=({0,1,2}:Set (Fin 8)) ∧
      {candidate | 0 ≤ actualValue 3-(1/5:ℝ)-actualDistance 3 candidate}=({2,3,4}:Set (Fin 8)) ∧
      {candidate | 0 ≤ actualValue 0-(1/5:ℝ)-actualDistance 0 candidate}=({0}:Set (Fin 8)) ∧
      {candidate | 0 ≤ actualValue 4-(1/5:ℝ)-actualDistance 4 candidate}=({4}:Set (Fin 8)) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals ext candidate
  all_goals fin_cases candidate <;> norm_num [actualValue,actualDistance]

end SafeLearning.CompleteModulesSafeOptEightPointRadii
