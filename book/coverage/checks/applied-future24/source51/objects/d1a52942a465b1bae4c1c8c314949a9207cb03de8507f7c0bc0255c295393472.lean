import SafeLearning.CompleteFoundationsExponentialNumerics
import SafeLearning.CompleteAppliedFiniteEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1200
noncomputable section
open scoped BigOperators
open MeasureTheory InformationTheory

namespace SafeLearning.CompletePolicyFOCOPSNumbers20
open SafeLearning.CompleteFoundationsExponentialNumerics
open SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedFiniteKL

theorem actual_logarithm_enclosure_from_exponential_polynomials
    (x lo hi : ℝ) (hx : 0 < x) (hlo : |lo| ≤ 1) (hhi : |hi| ≤ 1)
    (hl : expPolynomial lo + 1 / 100000000000000000 < x)
    (hu : x < expPolynomial hi - 1 / 100000000000000000) :
    lo < Real.log x ∧ Real.log x < hi := by
  have el := actual_twentieth_exponential_polynomial_error_on_the_unit_interval lo hlo
  have eu := actual_twentieth_exponential_polynomial_error_on_the_unit_interval hi hhi
  rw [abs_le] at el eu
  constructor
  · apply (Real.lt_log_iff_exp_lt hx).mpr
    linarith [el.2]
  · apply (Real.log_lt_iff_lt_exp hx).mpr
    linarith [eu.1]

theorem actual_log_five_fourths_enclosure :
    (223143551 / 1000000000 : ℝ) < Real.log (5 / 4) ∧
      Real.log (5 / 4) < (223143552 / 1000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_log_four_thirds_enclosure :
    (287682072 / 1000000000 : ℝ) < Real.log (4 / 3) ∧
      Real.log (4 / 3) < (287682073 / 1000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem actual_log_five_thirds_enclosure :
    (510825623 / 1000000000 : ℝ) < Real.log (5 / 3) ∧
      Real.log (5 / 3) < (510825624 / 1000000000 : ℝ) := by
  apply actual_logarithm_enclosure_from_exponential_polynomials
  · norm_num
  · norm_num
  · norm_num
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  · norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

def binaryKLExpression (p : ℝ) : ℝ :=
  p * Real.log (2 * p) + (1 - p) * Real.log (2 * (1 - p))

theorem actual_any_two_action_policy_true_uniform_kl
    (law : PMF (Fin 2)) :
    (klDiv law.toMeasure (PMF.uniformOfFintype (Fin 2)).toMeasure).toReal =
      binaryKLExpression (law 0).toReal := by
  have hmass := actual_finite_weights_sum law
  simp only [Fin.sum_univ_two] at hmass
  have h1 : (law 1).toReal = 1 - (law 0).toReal := by linarith
  rw [actual_finite_kl_sum law _ (fun i => PMF.mem_support_uniformOfFintype i)]
  simp only [Fin.sum_univ_two, actual_uniform_mass]
  norm_num [binaryKLExpression, h1]
  ring

theorem actual_five_eighths_binary_kl_exact_logarithms :
    binaryKLExpression (5 / 8) =
      (5 / 8 : ℝ) * Real.log (5 / 4) - (3 / 8 : ℝ) * Real.log (4 / 3) := by
  have hlog : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  norm_num [binaryKLExpression]
  rw [hlog]
  ring

theorem actual_five_eighths_kl_enclosure_and_both_budget_comparisons :
    (31583941 / 1000000000 : ℝ) < binaryKLExpression (5 / 8) ∧
      binaryKLExpression (5 / 8) < (31583943 / 1000000000 : ℝ) ∧
      (1 / 50 : ℝ) < binaryKLExpression (5 / 8) ∧
      binaryKLExpression (5 / 8) < (1 / 20 : ℝ) := by
  have h1 := actual_log_five_fourths_enclosure
  have h2 := actual_log_four_thirds_enclosure
  rw [actual_five_eighths_binary_kl_exact_logarithms]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem actual_five_eighths_policy_true_kl_has_the_source_rounded_value
    (law : PMF (Fin 2)) (h : (law 0).toReal = 5 / 8) :
    |(klDiv law.toMeasure (PMF.uniformOfFintype (Fin 2)).toMeasure).toReal -
        (316 / 10000 : ℝ)| < 1 / 20000 ∧
      (klDiv law.toMeasure (PMF.uniformOfFintype (Fin 2)).toMeasure).toReal ≠
        (316 / 10000 : ℝ) ∧
      (1 / 50 : ℝ) <
        (klDiv law.toMeasure (PMF.uniformOfFintype (Fin 2)).toMeasure).toReal ∧
      (klDiv law.toMeasure (PMF.uniformOfFintype (Fin 2)).toMeasure).toReal <
        (1 / 20 : ℝ) := by
  rw [actual_any_two_action_policy_true_uniform_kl, h]
  have hb := actual_five_eighths_kl_enclosure_and_both_budget_comparisons
  refine ⟨?_, ?_, hb.2.2.1, hb.2.2.2⟩
  · rw [abs_lt]; constructor <;> linarith [hb.1, hb.2.1]
  · exact ne_of_lt (by linarith [hb.2.1])

theorem actual_source_logarithm_and_weighted_terms_roundings_not_equalities :
    |Real.log (5 / 3 : ℝ) - 511 / 1000| < 1 / 2000 ∧
      Real.log (5 / 3 : ℝ) ≠ 511 / 1000 ∧
      |(5 / 8 : ℝ) * Real.log (5 / 4) - 1395 / 10000| < 1 / 20000 ∧
      (5 / 8 : ℝ) * Real.log (5 / 4) ≠ 1395 / 10000 ∧
      |(3 / 8 : ℝ) * Real.log (4 / 3) - 1079 / 10000| < 1 / 20000 ∧
      (3 / 8 : ℝ) * Real.log (4 / 3) ≠ 1079 / 10000 := by
  have h1 := actual_log_five_fourths_enclosure
  have h2 := actual_log_four_thirds_enclosure
  have h3 := actual_log_five_thirds_enclosure
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith [h3.2])
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith [h1.2])
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_lt (by linarith [h2.2])

theorem actual_temperature_one_cost_price_enclosure_rounding_and_non_equality :
    (372293594 / 1000000000 : ℝ) < 1 / 2 - Real.log (5 / 3) / 4 ∧
      1 / 2 - Real.log (5 / 3) / 4 < (372293595 / 1000000000 : ℝ) ∧
      |(1 / 2 - Real.log (5 / 3) / 4 : ℝ) - 372 / 1000| < 1 / 2000 ∧
      (1 / 2 - Real.log (5 / 3) / 4 : ℝ) ≠ 372 / 1000 ∧
      (0 : ℝ) < 1 / 2 - Real.log (5 / 3) / 4 := by
  have h := actual_log_five_thirds_enclosure
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_gt (by linarith [h.2])
  · linarith

theorem actual_nonnegative_cost_price_temperature_threshold_and_rounding :
    (3915230 / 1000000 : ℝ) < 2 / Real.log (5 / 3) ∧
      2 / Real.log (5 / 3) < (3915231 / 1000000 : ℝ) ∧
      |(2 / Real.log (5 / 3) : ℝ) - 3915 / 1000| < 1 / 2000 ∧
      (2 / Real.log (5 / 3) : ℝ) ≠ 3915 / 1000 := by
  have h := actual_log_five_thirds_enclosure
  have hp : 0 < Real.log (5 / 3 : ℝ) := by linarith [h.1]
  have hlo : (3915230 / 1000000 : ℝ) < 2 / Real.log (5 / 3) := by
    rw [lt_div_iff₀ hp]
    nlinarith [h.2]
  have hhi : 2 / Real.log (5 / 3) < (3915231 / 1000000 : ℝ) := by
    rw [div_lt_iff₀ hp]
    nlinarith [h.1]
  refine ⟨hlo, hhi, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · exact ne_of_gt (by linarith)

end SafeLearning.CompletePolicyFOCOPSNumbers20
