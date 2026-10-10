import SafeLearning.CompleteFoundationsExponentialNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace SafeLearning.CompletePolicyFOCOPSProbabilityNumbers20
open SafeLearning.CompleteFoundationsExponentialNumerics

def binaryExponentialProbability (u : ℝ) : ℝ :=
  Real.exp u / (Real.exp u + Real.exp (-u))

theorem actual_binary_exponential_probability_positive_square_form (u : ℝ) :
    binaryExponentialProbability u = (Real.exp u) ^ 2 / ((Real.exp u) ^ 2 + 1) := by
  rw [binaryExponentialProbability, Real.exp_neg]
  have hp := (Real.exp_pos u).ne'
  field_simp
  ring

theorem actual_temperature_one_unpriced_probability_and_reward_roundings :
    (880797077 / 1000000000 : ℝ) < binaryExponentialProbability 1 ∧
      binaryExponentialProbability 1 < (880797079 / 1000000000 : ℝ) ∧
      |binaryExponentialProbability 1 - (881 / 1000 : ℝ)| < 1 / 2000 ∧
      binaryExponentialProbability 1 ≠ (881 / 1000 : ℝ) ∧
      |2 * binaryExponentialProbability 1 - 1 - (762 / 1000 : ℝ)| < 1 / 2000 ∧
      2 * binaryExponentialProbability 1 - 1 ≠ (762 / 1000 : ℝ) ∧
      (5 / 8 : ℝ) < binaryExponentialProbability 1 := by
  have he := actual_exponential_rational_enclosures_needed_by_the_source
  have hp : 0 < (Real.exp 1) ^ 2 + 1 := by positivity
  have hl : (880797077 / 1000000000 : ℝ) <
      (Real.exp 1) ^ 2 / ((Real.exp 1) ^ 2 + 1) := by
    rw [lt_div_iff₀ hp]
    have he2 := pow_lt_pow_left₀ he.1 (by norm_num : (0 : ℝ) ≤ 2718281828 / 1000000000)
      (by norm_num : (2 : ℕ) ≠ 0)
    norm_num1 at he2
    nlinarith
  have hu : (Real.exp 1) ^ 2 / ((Real.exp 1) ^ 2 + 1) <
      (880797079 / 1000000000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    have he2 := pow_lt_pow_left₀ he.2.1 (Real.exp_pos 1).le
      (by norm_num : (2 : ℕ) ≠ 0)
    norm_num1 at he2
    nlinarith
  rw [← actual_binary_exponential_probability_positive_square_form] at hl hu
  refine ⟨hl, hu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)
  · linarith

theorem actual_exponential_one_sixth_enclosure :
    (1181360412 / 1000000000 : ℝ) < Real.exp (1 / 6) ∧
      Real.exp (1 / 6) < (1181360413 / 1000000000 : ℝ) := by
  have he := actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (1 / 6 : ℝ) (by norm_num)
  norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial, abs_le] at he
  constructor <;> linarith

theorem actual_temperature_six_unpriced_probability_rounding_and_slack :
    (582570206 / 1000000000 : ℝ) < binaryExponentialProbability (1 / 6) ∧
      binaryExponentialProbability (1 / 6) < (582570208 / 1000000000 : ℝ) ∧
      |binaryExponentialProbability (1 / 6) - (583 / 1000 : ℝ)| < 1 / 2000 ∧
      binaryExponentialProbability (1 / 6) ≠ (583 / 1000 : ℝ) ∧
      binaryExponentialProbability (1 / 6) < (5 / 8 : ℝ) := by
  have he := actual_exponential_one_sixth_enclosure
  have hp : 0 < (Real.exp (1 / 6)) ^ 2 + 1 := by positivity
  have hl : (582570206 / 1000000000 : ℝ) <
      (Real.exp (1 / 6)) ^ 2 / ((Real.exp (1 / 6)) ^ 2 + 1) := by
    rw [lt_div_iff₀ hp]
    have he2 := pow_lt_pow_left₀ he.1
      (by norm_num : (0 : ℝ) ≤ 1181360412 / 1000000000) (by norm_num : (2 : ℕ) ≠ 0)
    norm_num1 at he2
    nlinarith
  have hu : (Real.exp (1 / 6)) ^ 2 / ((Real.exp (1 / 6)) ^ 2 + 1) <
      (582570208 / 1000000000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    have he2 := pow_lt_pow_left₀ he.2 (Real.exp_pos (1 / 6)).le
      (by norm_num : (2 : ℕ) ≠ 0)
    norm_num1 at he2
    nlinarith
  rw [← actual_binary_exponential_probability_positive_square_form] at hl hu
  refine ⟨hl, hu, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)
  · linarith

theorem actual_cost_tight_multiplier_is_nonnegative_iff_temperature_threshold (lam : ℝ) :
    0 ≤ 1 / 2 - lam / 4 * Real.log (5 / 3) ↔ lam ≤ 2 / Real.log (5 / 3) := by
  have hp : 0 < Real.log (5 / 3 : ℝ) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

theorem actual_cost_tight_multiplier_gives_exact_five_eighths_policy
    (lam : ℝ) (hlam : 0 < lam) :
    binaryExponentialProbability ((1 - 2 * (1 / 2 - lam / 4 * Real.log (5 / 3))) / lam) =
      5 / 8 := by
  let u := (1 - 2 * (1 / 2 - lam / 4 * Real.log (5 / 3))) / lam
  have h2u : 2 * u = Real.log (5 / 3) := by
    dsimp [u]
    field_simp
    ring
  have hr : Real.exp u / Real.exp (-u) = (5 / 3 : ℝ) := by
    rw [← Real.exp_sub, show u - -u = 2 * u by ring, h2u,
      Real.exp_log (by norm_num)]
  have hc : Real.exp u = (5 / 3 : ℝ) * Real.exp (-u) :=
    (div_eq_iff (Real.exp_pos (-u)).ne').mp hr
  change Real.exp u / (Real.exp u + Real.exp (-u)) = 5 / 8
  apply (div_eq_iff (add_pos (Real.exp_pos u) (Real.exp_pos (-u))).ne').mpr
  linarith

end SafeLearning.CompletePolicyFOCOPSProbabilityNumbers20
