import SafeLearning.CompleteAppliedViabilityKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedViabilityPrecision
open CompleteAppliedViabilityKernel

theorem actual_source_backward_radius_fixed_point_iff (c : ℝ) :
    c = (c+3/10)/(3/2) ↔ c = 3/5 := by
  constructor <;> intro h <;> linarith

theorem actual_four_displayed_decimal_radii_are_strictly_rounded :
    radius 1 < (867/1000:ℝ) ∧ radius 2 < (778/1000:ℝ) ∧
      radius 3 < (719/1000:ℝ) ∧ radius 4 > (679/1000:ℝ) := by
  norm_num [radius]

theorem actual_four_displayed_decimal_radii_are_not_exact :
    radius 1 ≠ (867/1000:ℝ) ∧ radius 2 ≠ (778/1000:ℝ) ∧
      radius 3 ≠ (719/1000:ℝ) ∧ radius 4 ≠ (679/1000:ℝ) := by
  norm_num [radius]

end SafeLearning.CompleteAppliedViabilityPrecision
