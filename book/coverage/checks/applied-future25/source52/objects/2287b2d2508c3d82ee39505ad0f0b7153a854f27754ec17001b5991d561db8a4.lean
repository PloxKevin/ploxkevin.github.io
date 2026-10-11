import SafeLearning.CompleteAppliedRiskPrimer

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedRiskPrecision

theorem actual_source_standard_deviation_is_not_exact_printed_decimal :
    Real.sqrt (124 / 25 : ℝ) ≠ 2227 / 1000 := by
  intro h
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (124 / 25 : ℝ))
  rw [h] at hs
  norm_num at hs

theorem actual_rounded_input_product_and_precision :
    (4 / 5 : ℝ) + (2227 / 1000) * (351 / 200) = 941677 / 200000 ∧
    (941677 / 200000 : ℝ) ≠ 471 / 100 ∧
    |(941677 / 200000 : ℝ) - 471 / 100| < 1 / 200 ∧
    (6 : ℝ) - 941677 / 200000 = 258323 / 200000 ∧
    |(258323 / 200000 : ℝ) - 13 / 10| < 1 / 20 := by
  norm_num

end SafeLearning.CompleteAppliedRiskPrecision
