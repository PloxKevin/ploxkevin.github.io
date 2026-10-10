import SafeLearning.CompleteAppliedInformation

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyUnits
open MeasureTheory
open SafeLearning.CompleteAppliedInformation

def natToBits (amount : ℝ) : ℝ := amount / Real.log 2

def entropyBits {n : ℕ} (p : PMF (Fin n)) : ℝ :=
  -(∫ i, Real.logb 2 ((p i).toReal) ∂p.toMeasure)

theorem actual_natural_to_base_two_entropy_units {n : ℕ} (p : PMF (Fin n)) :
    entropyBits p = natToBits (shannonEntropy p) := by
  exact actual_entropy_in_bits p

theorem actual_one_nat_bits_conversion : natToBits 1 = 1 / Real.log 2 := rfl

theorem actual_one_nat_bits_six_decimal_rounding :
    |natToBits 1 - (1442695 / 1000000 : ℝ)| < 1 / 2000000 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hlow : (1442695 / 1000000 : ℝ) - 1 / 2000000 < 1 / Real.log 2 := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith
  have hhigh : 1 / Real.log 2 < (1442695 / 1000000 : ℝ) + 1 / 2000000 := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  unfold natToBits
  rw [abs_lt]
  constructor <;> linarith

theorem actual_one_nat_bits_two_decimal_rounding :
    |natToBits 1 - (144 / 100 : ℝ)| < 1 / 200 := by
  have h := actual_one_nat_bits_six_decimal_rounding
  rw [abs_lt] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem actual_unit_conversion_is_positive_linear_and_invertible (x y scalar : ℝ) :
    natToBits (x + y) = natToBits x + natToBits y ∧
    natToBits (scalar * x) = scalar * natToBits x ∧
    natToBits x * Real.log 2 = x ∧
    (0 ≤ natToBits x ↔ 0 ≤ x) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by simp [natToBits, add_div], by simp [natToBits, mul_div_assoc], ?_, ?_⟩
  · exact div_mul_cancel₀ x (ne_of_gt hp)
  · unfold natToBits
    constructor
    · intro h
      have hm := mul_nonneg h hp.le
      rw [div_mul_cancel₀ x (ne_of_gt hp)] at hm
      exact hm
    · intro h
      exact div_nonneg h hp.le

end SafeLearning.CompleteAppliedEntropyUnits
