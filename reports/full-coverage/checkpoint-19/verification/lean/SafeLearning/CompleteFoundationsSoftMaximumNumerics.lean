import SafeLearning.CompleteFoundationsExponentialLesson
import SafeLearning.CompleteFoundationsExponentialNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsSoftMaximumNumerics
open CompleteFoundationsExponentialLesson CompleteFoundationsExponentialNumerics

def sourceScores : Fin 3 → ℝ := ![1, 1 / 2, 9 / 10]
def normalizedSum (alpha : ℝ) : ℝ :=
  1 + Real.exp (-1 / (2 * alpha)) + Real.exp (-1 / (10 * alpha))

theorem actual_source_maximum_and_soft_maximum_normalization
    (alpha : ℝ) (ha : 0 < alpha) :
    actualMaximum sourceScores = 1 ∧
      actualSoftMaximum sourceScores alpha = 1 + alpha * Real.log (normalizedSum alpha) := by
  have hm := actual_finite_maximum_is_attained_and_bounds_every_entry sourceScores
  have hupper (i : Fin 3) : sourceScores i ≤ 1 := by fin_cases i <;> norm_num [sourceScores]
  have hmax : actualMaximum sourceScores = 1 := by
    obtain ⟨⟨i, hi⟩, hb⟩ := hm
    have hlo : 1 ≤ actualMaximum sourceScores := by simpa [sourceScores] using hb 0
    have hup : actualMaximum sourceScores ≤ 1 := by rw [hi]; exact hupper i
    exact le_antisymm hup hlo
  refine ⟨hmax, ?_⟩
  have he (a : ℝ) : Real.exp (a / alpha) =
      Real.exp (1 / alpha) * Real.exp ((a - 1) / alpha) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hs : (∑ i, Real.exp (sourceScores i / alpha)) =
      Real.exp (1 / alpha) * normalizedSum alpha := by
    simp only [Fin.sum_univ_succ, sourceScores, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    rw [he (1 / 2), he (9 / 10)]
    have ha₁ : ((1 / 2 : ℝ) - 1) / alpha = -1 / (2 * alpha) := by field_simp; ring
    have ha₂ : ((9 / 10 : ℝ) - 1) / alpha = -1 / (10 * alpha) := by field_simp; ring
    rw [ha₁, ha₂]
    unfold normalizedSum
    ring
  have hn : 0 < normalizedSum alpha := by unfold normalizedSum; positivity
  unfold actualSoftMaximum
  rw [hs, Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp]
  field_simp

theorem actual_source_comparison_exponentials_have_rational_bounds :
    Real.exp (9205 / 10000 : ℝ) < 2511 / 1000 ∧
      (25115 / 10000 : ℝ) < Real.exp (921 / 1000) ∧
      Real.exp (315 / 1000 : ℝ) < 1371 / 1000 ∧
      (1377 / 1000 : ℝ) < Real.exp (32 / 100) := by
  have h₁ := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (9205 / 10000 : ℝ) (by norm_num)
  have h₂ := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (921 / 1000 : ℝ) (by norm_num)
  have h₃ := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (315 / 1000 : ℝ) (by norm_num)
  have h₄ := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (32 / 100 : ℝ) (by norm_num)
  norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial, abs_le] at h₁ h₂ h₃ h₄
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem actual_negative_exponentials_have_rational_bounds :
    (6065 / 10000 : ℝ) < Real.exp (-(1 / 2)) ∧
      Real.exp (-(1 / 2) : ℝ) < 6066 / 10000 ∧
      (9048 / 10000 : ℝ) < Real.exp (-(1 / 10)) ∧
      Real.exp (-(1 / 10) : ℝ) < 9049 / 10000 ∧
      (67 / 10000 : ℝ) < Real.exp (-5) ∧ Real.exp (-5 : ℝ) < 68 / 10000 ∧
      (453999 / 10000000000 : ℝ) < Real.exp (-10) ∧
      Real.exp (-10 : ℝ) < 454000 / 10000000000 ∧
      Real.exp (-50 : ℝ) < 1 / 100000000000000000000 := by
  have h := actual_exponential_rational_enclosures_needed_by_the_source
  have hpow (n : ℕ) : Real.exp (-(n : ℝ)) = 1 / (Real.exp 1) ^ n := by
    rw [Real.exp_neg, one_div]
    congr 1
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  have bound (n : ℕ) (hn : n ≠ 0) :
      (2718281828 / 1000000000 : ℝ) ^ n < (Real.exp 1) ^ n ∧
      (Real.exp 1) ^ n < (2718281829 / 1000000000 : ℝ) ^ n := by
    exact ⟨pow_lt_pow_left₀ h.1 (by norm_num) hn,
      pow_lt_pow_left₀ h.2.1 (Real.exp_pos 1).le hn⟩
  have h₅ := bound 5 (by norm_num)
  have h₁₀ := bound 10 (by norm_num)
  have h₅₀ := bound 50 (by norm_num)
  norm_num1 at h₅ h₁₀ h₅₀
  have hp := Real.exp_pos (1 : ℝ)
  have he₅ : Real.exp (-5 : ℝ) = 1 / Real.exp 1 ^ 5 := by
    simpa only [Nat.cast_ofNat] using hpow 5
  have he₁₀ : Real.exp (-10 : ℝ) = 1 / Real.exp 1 ^ 10 := by
    simpa only [Nat.cast_ofNat] using hpow 10
  have he₅₀ : Real.exp (-50 : ℝ) = 1 / Real.exp 1 ^ 50 := by
    simpa only [Nat.cast_ofNat] using hpow 50
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.exp_neg, ← one_div, lt_div_iff₀ (Real.exp_pos _)]; nlinarith [h.2.2.1]
  · rw [Real.exp_neg, ← one_div, div_lt_iff₀ (Real.exp_pos _)]; nlinarith [h.2.2.2.1]
  · rw [Real.exp_neg, ← one_div, lt_div_iff₀ (Real.exp_pos _)]; nlinarith [h.2.2.2.2.1]
  · rw [Real.exp_neg, ← one_div, div_lt_iff₀ (Real.exp_pos _)]; nlinarith [h.2.2.2.2.2]
  · rw [he₅, lt_div_iff₀ (pow_pos hp 5)]; nlinarith [h₅.2]
  · rw [he₅, div_lt_iff₀ (pow_pos hp 5)]; nlinarith [h₅.1]
  · rw [he₁₀, lt_div_iff₀ (pow_pos hp 10)]; nlinarith [h₁₀.2]
  · rw [he₁₀, div_lt_iff₀ (pow_pos hp 10)]; nlinarith [h₁₀.1]
  · rw [he₅₀, div_lt_iff₀ (pow_pos hp 50)]; nlinarith [h₅₀.1]

theorem actual_source_soft_maximum_values_are_certified_roundings_and_strict_non_equalities :
    |actualSoftMaximum sourceScores 1 - (1921 / 1000 : ℝ)| < 1 / 2000 ∧
      actualSoftMaximum sourceScores 1 < (1921 / 1000 : ℝ) ∧
      |actualSoftMaximum sourceScores (1 / 10) - (1032 / 1000 : ℝ)| < 1 / 2000 ∧
      actualSoftMaximum sourceScores (1 / 10) < (1032 / 1000 : ℝ) ∧
      |actualSoftMaximum sourceScores (1 / 100) - (10000005 / 10000000 : ℝ)| <
        1 / 20000000 ∧
      actualSoftMaximum sourceScores (1 / 100) < (10000005 / 10000000 : ℝ) := by
  have hn := actual_negative_exponentials_have_rational_bounds
  have he := actual_source_comparison_exponentials_have_rational_bounds
  have hsum₁ : Real.exp (9205 / 10000 : ℝ) < normalizedSum 1 ∧
      normalizedSum 1 < Real.exp (921 / 1000 : ℝ) := by
    norm_num only [normalizedSum]
    constructor <;> linarith [he.1, he.2.1, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1]
  have hsum₂ : Real.exp (315 / 1000 : ℝ) < normalizedSum (1 / 10) ∧
      normalizedSum (1 / 10) < Real.exp (32 / 100 : ℝ) := by
    norm_num only [normalizedSum]
    have hi := actual_e_and_inverse_e_roundings_and_strict_non_equalities.2.2.1
    simp only [show Real.exp (-1 : ℝ) = 1 / Real.exp 1 by rw [Real.exp_neg, one_div]]
    rw [abs_lt] at hi
    constructor <;> linarith [he.2.2.1, he.2.2.2, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hi.1, hi.2]
  have hp (a : ℝ) : 0 < normalizedSum a := by unfold normalizedSum; positivity
  have hl₁ : (9205 / 10000 : ℝ) < Real.log (normalizedSum 1) ∧
      Real.log (normalizedSum 1) < 921 / 1000 := by
    exact ⟨by simpa using Real.log_lt_log (Real.exp_pos _) hsum₁.1,
      by simpa using Real.log_lt_log (hp 1) hsum₁.2⟩
  have hl₂ : (315 / 1000 : ℝ) < Real.log (normalizedSum (1 / 10)) ∧
      Real.log (normalizedSum (1 / 10)) < 32 / 100 := by
    exact ⟨by simpa using Real.log_lt_log (Real.exp_pos _) hsum₂.1,
      by simpa using Real.log_lt_log (hp _) hsum₂.2⟩
  have hs₃ : (1 + 453999 / 10000000000 : ℝ) < normalizedSum (1 / 100) ∧
      normalizedSum (1 / 100) < 1 + 454000 / 10000000000 + 1 / 100000000000000000000 := by
    norm_num only [normalizedSum]
    constructor <;> linarith [hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.2, Real.exp_pos (-50 : ℝ)]
  have hl₃ : (45 / 1000000 : ℝ) < Real.log (normalizedSum (1 / 100)) ∧
      Real.log (normalizedSum (1 / 100)) < 5 / 100000 := by
    have hu := Real.log_le_sub_one_of_pos (hp (1 / 100))
    have hd := Real.log_le_sub_one_of_pos (inv_pos.mpr (hp (1 / 100)))
    rw [Real.log_inv] at hd
    have hid : normalizedSum (1 / 100) * (normalizedSum (1 / 100))⁻¹ = 1 :=
      mul_inv_cancel₀ (hp _).ne'
    have hlow : (45 / 1000000 : ℝ) < 1 - (normalizedSum (1 / 100))⁻¹ := by
      nlinarith [hs₃.1]
    constructor <;> linarith [hs₃.2]
  rw [(actual_source_maximum_and_soft_maximum_normalization 1 (by norm_num)).2,
    (actual_source_maximum_and_soft_maximum_normalization (1 / 10) (by norm_num)).2,
    (actual_source_maximum_and_soft_maximum_normalization (1 / 100) (by norm_num)).2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try rw [abs_lt])
  all_goals (try constructor)
  all_goals linarith [hl₁.1, hl₁.2, hl₂.1, hl₂.2, hl₃.1, hl₃.2]

end SafeLearning.CompleteFoundationsSoftMaximumNumerics
