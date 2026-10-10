import SafeLearning.CompleteModulesGoSafeToyGridLipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyGridConstantConsequences
open SafeLearning.CompleteModulesGoSafeToyGridLipschitz

theorem actual_source_exact_real_grid_lipschitz_constant_has_the_printed_two_decimal_rounding :
    |(128/15:ℝ)-(853/100)| < 1/200 ∧ (128/15:ℝ) ≠ 853/100 := by norm_num

theorem actual_source_exact_real_grid_lipschitz_constant_is_the_least_global_grid_bound :
    IsLeast {constant : ℝ | ∀ p q : GridPoint,
      |actualGridSafety p-actualGridSafety q| ≤ constant*actualGridDistance p q} (128/15:ℝ) := by
  constructor
  · exact actual_source_grid_difference_is_bounded_by_the_exact_grid_euclidean_constant
  · intro constant hc
    have hmax := actual_source_grid_has_the_largest_difference_quotient_one_hundred_twenty_eight_over_fifteen
    obtain ⟨p,q,hne,heq⟩ := hmax.1
    have hd := actual_source_grid_distance_is_positive_for_distinct_grid_points p q hne
    have hb := hc p q
    have hr : |actualGridSafety p-actualGridSafety q|/actualGridDistance p q ≤ constant :=
      (div_le_iff₀ hd).mpr hb
    rw [← heq] at hr
    exact hr

end SafeLearning.CompleteModulesGoSafeToyGridConstantConsequences
