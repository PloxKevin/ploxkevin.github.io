import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesFiniteSumPerturbation

theorem actual_weighted_finite_sum_error_is_bounded_by_component_error_and_total_weight
    {I : Type*} [Fintype I] (first second weight : I → ℝ) (tolerance : ℝ)
    (herror : ∀ i, |first i-second i| ≤ tolerance) :
    |(∑ i, first i*weight i)-(∑ i, second i*weight i)| ≤
      tolerance*(∑ i, |weight i|) := by
  calc
    _ = |∑ i, (first i-second i)*weight i| := by
      congr 1
      simp only [sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(first i-second i)*weight i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, tolerance*|weight i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (herror i) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem actual_two_factor_finite_sum_error_has_separate_weight_and_data_bounds
    {I : Type*} [Fintype I] (weight approximateWeight data approximateData : I → ℝ)
    (weightTolerance dataTolerance : ℝ)
    (hweight : ∀ i, |weight i-approximateWeight i| ≤ weightTolerance)
    (hdata : ∀ i, |data i-approximateData i| ≤ dataTolerance) :
    |(∑ i, weight i*data i)-(∑ i, approximateWeight i*approximateData i)| ≤
      weightTolerance*(∑ i, |data i|)+dataTolerance*(∑ i, |approximateWeight i|) := by
  calc
    _ ≤ |(∑ i, weight i*data i)-(∑ i, approximateWeight i*data i)|+
      |(∑ i, approximateWeight i*data i)-(∑ i, approximateWeight i*approximateData i)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      apply add_le_add
      · exact actual_weighted_finite_sum_error_is_bounded_by_component_error_and_total_weight
          weight approximateWeight data weightTolerance hweight
      · simpa only [mul_comm] using
          actual_weighted_finite_sum_error_is_bounded_by_component_error_and_total_weight
            data approximateData approximateWeight dataTolerance hdata

end SafeLearning.CompleteModulesFiniteSumPerturbation
