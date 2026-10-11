import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1200
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsExponentialNumerics

def expPolynomial (x : ℝ) : ℝ := ∑ i ∈ Finset.range 20, x ^ i / (i.factorial : ℝ)

theorem actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - expPolynomial x| ≤ 1 / 100000000000000000 := by
  have hr : ‖(x : ℂ)‖ / (20 + 1 : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    linarith
  have he := Complex.exp_bound' (x := (x : ℂ)) (n := 20) (by norm_num at hr ⊢; exact hr)
  have heReal : |Real.exp x - expPolynomial x| ≤ |x| ^ 20 / (20 : ℕ).factorial * 2 := by
    convert he using 1 <;> norm_cast
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 20
  norm_num [Nat.factorial] at heReal hp
  nlinarith

theorem actual_source_rational_power_values_have_the_printed_nearest_four_decimals :
    |(1 + 1 / 10 : ℝ) ^ 10 - 25937 / 10000| < 1 / 20000 ∧
      |(1 + 1 / 100 : ℝ) ^ 100 - 27048 / 10000| < 1 / 20000 ∧
      |(1 + 1 / 1000 : ℝ) ^ 1000 - 27169 / 10000| < 1 / 20000 ∧
      |(1 - 1 / 10 : ℝ) ^ 10 - 3487 / 10000| < 1 / 20000 ∧
      |(1 - 1 / 100 : ℝ) ^ 100 - 3660 / 10000| < 1 / 20000 ∧
      |(1 - 1 / 1000 : ℝ) ^ 1000 - 3677 / 10000| < 1 / 20000 := by
  norm_num

theorem actual_source_rational_power_displays_are_strictly_unequal_to_their_rounded_values :
    (1 + 1 / 10 : ℝ) ^ 10 ≠ 25937 / 10000 ∧
      (1 + 1 / 100 : ℝ) ^ 100 ≠ 27048 / 10000 ∧
      (1 + 1 / 1000 : ℝ) ^ 1000 ≠ 27169 / 10000 ∧
      (1 - 1 / 10 : ℝ) ^ 10 ≠ 3487 / 10000 ∧
      (1 - 1 / 100 : ℝ) ^ 100 ≠ 3660 / 10000 ∧
      (1 - 1 / 1000 : ℝ) ^ 1000 ≠ 3677 / 10000 := by
  norm_num

theorem actual_exponential_rational_enclosures_needed_by_the_source :
    (2718281828 / 1000000000 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 2718281829 / 1000000000 ∧
    (1648721270 / 1000000000 : ℝ) < Real.exp (1 / 2) ∧
      Real.exp (1 / 2) < 1648721271 / 1000000000 ∧
    (1105170918 / 1000000000 : ℝ) < Real.exp (1 / 10) ∧
      Real.exp (1 / 10) < 1105170919 / 1000000000 := by
  have h1 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval (1 : ℝ) (by norm_num)
  have h2 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval (1 / 2 : ℝ) (by norm_num)
  have h3 := actual_twentieth_exponential_polynomial_error_on_the_unit_interval (1 / 10 : ℝ) (by norm_num)
  norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial, abs_le] at h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem actual_e_and_inverse_e_roundings_and_strict_non_equalities :
    |Real.exp 1 - (271828 / 100000 : ℝ)| < 1 / 200000 ∧
      Real.exp 1 ≠ (271828 / 100000 : ℝ) ∧
      |1 / Real.exp 1 - (3679 / 10000 : ℝ)| < 1 / 20000 ∧
      1 / Real.exp 1 ≠ (3679 / 10000 : ℝ) := by
  have h := actual_exponential_rational_enclosures_needed_by_the_source
  have hp := Real.exp_pos (1 : ℝ)
  have hlo : (36785 / 100000 : ℝ) < 1 / Real.exp 1 := by
    rw [lt_div_iff₀ hp]
    nlinarith [h.1, h.2.1]
  have hhi : 1 / Real.exp 1 < (36795 / 100000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    nlinarith [h.1, h.2.1]
  have hne : 1 / Real.exp 1 < (3679 / 10000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    nlinarith [h.1]
  refine ⟨?_, ?_, ?_, ne_of_lt hne⟩
  · rw [abs_lt]; constructor <;> linarith [h.1, h.2.1]
  · exact ne_of_gt (by linarith [h.1])
  · rw [abs_lt]; constructor <;> linarith

theorem actual_source_miss_power_and_exponential_roundings_are_not_exact_equalities :
    |(99 / 100 : ℝ) ^ 300 - (49 / 1000 : ℝ)| < 1 / 2000 ∧
      (99 / 100 : ℝ) ^ 300 ≠ (49 / 1000 : ℝ) ∧
      |Real.exp (-3) - (498 / 10000 : ℝ)| < 1 / 20000 ∧
      Real.exp (-3) ≠ (498 / 10000 : ℝ) := by
  have h := actual_exponential_rational_enclosures_needed_by_the_source
  have hp : 0 < (Real.exp 1) ^ 3 := pow_pos (Real.exp_pos 1) 3
  have he : Real.exp (-3) = 1 / (Real.exp 1) ^ 3 := by
    rw [Real.exp_neg, one_div]
    congr 1
    simpa only [Nat.cast_ofNat, mul_one] using (Real.exp_nat_mul (1 : ℝ) 3)
  have hlo : (4975 / 100000 : ℝ) < 1 / (Real.exp 1) ^ 3 := by
    rw [lt_div_iff₀ hp]
    have hb := pow_lt_pow_left₀ h.2.1 (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
    norm_num1 at hb
    nlinarith
  have hhi : 1 / (Real.exp 1) ^ 3 < (4985 / 100000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    have hb := pow_lt_pow_left₀ h.1 (by norm_num : (0 : ℝ) ≤ 2718281828 / 1000000000)
      (by norm_num : (3 : ℕ) ≠ 0)
    norm_num1 at hb
    nlinarith
  have hne : 1 / (Real.exp 1) ^ 3 < (498 / 10000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    have hb := pow_lt_pow_left₀ h.1 (by norm_num : (0 : ℝ) ≤ 2718281828 / 1000000000)
      (by norm_num : (3 : ℕ) ≠ 0)
    norm_num1 at hb
    nlinarith
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [he, abs_lt]; constructor <;> linarith
  · rw [he]; exact ne_of_lt hne

end SafeLearning.CompleteFoundationsExponentialNumerics
