import SafeLearning.CompletePolicyFOCOPSHard20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1200
noncomputable section

namespace SafeLearning.CompletePolicyFOCOPSTightNumbers20
open SafeLearning.CompleteFoundationsExponentialNumerics
open SafeLearning.CompletePolicyFOCOPSNumbers20
open SafeLearning.CompletePolicyFOCOPSHard20

theorem actual_lower_root_endpoint_positive_logarithm :
    (181763401054 / 1000000000000 : ℝ) < Real.log (2 * (59966520 / 100000000 : ℝ)) ∧
      Real.log (2 * (59966520 / 100000000 : ℝ)) < (181763401055 / 1000000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_lower_root_endpoint_negative_logarithm :
    (-222306901404 / 1000000000000 : ℝ) < Real.log (2 * (1 - 59966520 / 100000000 : ℝ)) ∧
      Real.log (2 * (1 - 59966520 / 100000000 : ℝ)) < (-222306901403 / 1000000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_upper_root_endpoint_positive_logarithm :
    (181763417729 / 1000000000000 : ℝ) < Real.log (2 * (59966521 / 100000000 : ℝ)) ∧
      Real.log (2 * (59966521 / 100000000 : ℝ)) < (181763417730 / 1000000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_upper_root_endpoint_negative_logarithm :
    (-222306926383 / 1000000000000 : ℝ) < Real.log (2 * (1 - 59966521 / 100000000 : ℝ)) ∧
      Real.log (2 * (1 - 59966521 / 100000000 : ℝ)) < (-222306926382 / 1000000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_correct_root_endpoints_straddle_the_tight_KL_budget :
    binaryKLExpression (59966520 / 100000000) < (1 / 50 : ℝ) ∧
      (1 / 50 : ℝ) < binaryKLExpression (59966521 / 100000000) := by
  have hll := actual_lower_root_endpoint_positive_logarithm
  have hlr := actual_lower_root_endpoint_negative_logarithm
  have hul := actual_upper_root_endpoint_positive_logarithm
  have hur := actual_upper_root_endpoint_negative_logarithm
  unfold binaryKLExpression
  constructor <;> linarith

theorem actual_every_tight_KL_root_has_the_certified_eight_decimal_bracket
    (p : ℝ) (hp : p ∈ Set.Icc (1 / 2 : ℝ) (5 / 8))
    (he : binaryKLExpression p = 1 / 50) :
    (59966520 / 100000000 : ℝ) < p ∧ p < (59966521 / 100000000 : ℝ) := by
  have hlo : (59966520 / 100000000 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (5 / 8) := by norm_num
  have hhi : (59966521 / 100000000 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (5 / 8) := by norm_num
  have hb := actual_correct_root_endpoints_straddle_the_tight_KL_budget
  constructor
  · by_contra hn
    have hm := actual_binary_KL_strictly_increasing_above_half.monotoneOn hp hlo (le_of_not_gt hn)
    rw [he] at hm
    linarith [hb.1]
  · by_contra hn
    have hm := actual_binary_KL_strictly_increasing_above_half.monotoneOn hhi hp (le_of_not_gt hn)
    rw [he] at hm
    linarith [hb.2]

theorem actual_log_odds_is_the_difference_of_scaled_logarithms
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (p / (1 - p)) = Real.log (2 * p) - Real.log (2 * (1 - p)) := by
  rw [Real.log_div (ne_of_gt hp.1) (show 1 - p ≠ 0 by linarith [hp.2])]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp.1),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (show 1 - p ≠ 0 by linarith [hp.2])]
  ring

theorem actual_every_tight_KL_root_has_certified_log_odds
    (p : ℝ) (hp : p ∈ Set.Icc (1 / 2 : ℝ) (5 / 8))
    (he : binaryKLExpression p = 1 / 50) :
    (404070302457 / 1000000000000 : ℝ) < Real.log (p / (1 - p)) ∧
      Real.log (p / (1 - p)) < (404070344113 / 1000000000000 : ℝ) := by
  have hb := actual_every_tight_KL_root_has_the_certified_eight_decimal_bracket p hp he
  have hll := actual_lower_root_endpoint_positive_logarithm
  have hlr := actual_lower_root_endpoint_negative_logarithm
  have hul := actual_upper_root_endpoint_positive_logarithm
  have hur := actual_upper_root_endpoint_negative_logarithm
  have hlp := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 * (59966520 / 100000000 : ℝ))
    (show 2 * (59966520 / 100000000 : ℝ) < 2 * p by linarith)
  have hup := Real.log_lt_log (show 0 < 2 * p by linarith [hp.1])
    (show 2 * p < 2 * (59966521 / 100000000 : ℝ) by linarith)
  have hln := Real.log_lt_log (show 0 < 2 * (1 - p) by linarith [hp.2])
    (show 2 * (1 - p) < 2 * (1 - 59966520 / 100000000 : ℝ) by linarith)
  have hun := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 * (1 - 59966521 / 100000000 : ℝ))
    (show 2 * (1 - 59966521 / 100000000 : ℝ) < 2 * (1 - p) by linarith)
  rw [actual_log_odds_is_the_difference_of_scaled_logarithms p
    (by constructor <;> linarith [hp.1, hp.2])]
  constructor <;> linarith

theorem actual_every_tight_KL_root_multiplier_has_the_source_rounding
    (p : ℝ) (hp : p ∈ Set.Icc (1 / 2 : ℝ) (5 / 8))
    (he : binaryKLExpression p = 1 / 50) :
    (49496 / 10000 : ℝ) < 2 / Real.log (p / (1 - p)) ∧
      2 / Real.log (p / (1 - p)) < (49497 / 10000 : ℝ) ∧
      |2 / Real.log (p / (1 - p)) - (495 / 100 : ℝ)| < 1 / 200 ∧
      2 / Real.log (p / (1 - p)) ≠ (495 / 100 : ℝ) := by
  have hb := actual_every_tight_KL_root_has_certified_log_odds p hp he
  have hd : 0 < Real.log (p / (1 - p)) := by linarith [hb.1]
  have hl : (49496 / 10000 : ℝ) < 2 / Real.log (p / (1 - p)) := by
    rw [lt_div_iff₀ hd]
    linarith [hb.2]
  have hu : 2 / Real.log (p / (1 - p)) < (49497 / 10000 : ℝ) := by
    rw [div_lt_iff₀ hd]
    linarith [hb.1]
  refine ⟨hl, hu, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)

theorem actual_every_tight_KL_root_probability_cost_and_reward_roundings
    (p : ℝ) (hp : p ∈ Set.Icc (1 / 2 : ℝ) (5 / 8))
    (he : binaryKLExpression p = 1 / 50) :
    |p - (5997 / 10000 : ℝ)| < 1 / 20000 ∧ p ≠ (5997 / 10000 : ℝ) ∧
      |(4 * p - 2) - (399 / 1000 : ℝ)| < 1 / 2000 ∧
      (4 * p - 2) ≠ (399 / 1000 : ℝ) ∧
      |(2 * p - 1) - (1993 / 10000 : ℝ)| < 1 / 20000 ∧
      (2 * p - 1) ≠ (1993 / 10000 : ℝ) ∧ 4 * p - 2 < 1 / 2 := by
  have hb := actual_every_tight_KL_root_has_the_certified_eight_decimal_bracket p hp he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith)
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_gt (by linarith)
  · linarith

theorem actual_three_fifths_positive_logarithm :
    (182321556793 / 1000000000000 : ℝ) < Real.log (6 / 5) ∧
      Real.log (6 / 5) < (182321556794 / 1000000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_three_fifths_KL_exceeds_the_budget_and_rounds_to_point0201 :
    (1 / 50 : ℝ) < binaryKLExpression (3 / 5) ∧
      |binaryKLExpression (3 / 5) - (201 / 10000 : ℝ)| < 1 / 20000 ∧
      binaryKLExpression (3 / 5) ≠ (201 / 10000 : ℝ) := by
  have hp := actual_three_fifths_positive_logarithm
  have hn := actual_log_five_fourths_enclosure
  have hi : Real.log (4 / 5 : ℝ) = -Real.log (5 / 4 : ℝ) := by
    rw [show (4 / 5 : ℝ) = (5 / 4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have he : binaryKLExpression (3 / 5) =
      (3 / 5 : ℝ) * Real.log (6 / 5) - (2 / 5 : ℝ) * Real.log (5 / 4) := by
    norm_num [binaryKLExpression]
    rw [hi]
    ring
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_gt (by linarith)

end SafeLearning.CompletePolicyFOCOPSTightNumbers20
