import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace SafeLearning.CompleteFoundationsConvergenceRateExamples

theorem actual_quadratic_error_recursion_gives_the_double_exponential_prefix_bound
    (error : ℕ → ℝ) (coefficient : ℝ) (hc : 0 < coefficient)
    (he : ∀ n, 0 ≤ error n)
    (hstep : ∀ n, error (n + 1) ≤ coefficient * error n ^ 2) :
    ∀ n, coefficient * error n ≤ (coefficient * error 0) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      coefficient * error (n + 1) ≤ coefficient * (coefficient * error n ^ 2) :=
        mul_le_mul_of_nonneg_left (hstep n) hc.le
      _ = (coefficient * error n) ^ 2 := by ring
      _ ≤ ((coefficient * error 0) ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hc.le (he n)) ih 2
      _ = (coefficient * error 0) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]

theorem actual_quadratic_errors_converge_in_the_true_small_initial_error_domain
    (error : ℕ → ℝ) (coefficient : ℝ) (hc : 0 < coefficient)
    (he : ∀ n, 0 ≤ error n)
    (hsmall : coefficient * error 0 < 1)
    (hstep : ∀ n, error (n + 1) ≤ coefficient * error n ^ 2) :
    Tendsto error atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (coefficient * error 0) ^ (2 ^ n))
      atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hc.le (he 0)) hsmall).comp
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num))
  have scaled : Tendsto (fun n => coefficient * error n) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg hc.le (he n))
      (actual_quadratic_error_recursion_gives_the_double_exponential_prefix_bound
        error coefficient hc he hstep) ht
  convert scaled.div_const coefficient using 1 <;> simp [hc.ne']

theorem actual_polynomial_reciprocal_errors_converge_to_zero (power : ℝ)
    (hp : 0 < power) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-power)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop

theorem actual_every_positive_geometric_rate_is_little_o_of_each_polynomial_reciprocal
    (q power : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (fun n : ℕ => q ^ n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-power)) := by
  have ht := (isLittleO_exp_neg_mul_rpow_atTop
    (neg_pos.mpr (Real.log_neg hq0 hq1)) (-power)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  convert ht using 1
  · ext n
    change q ^ n = Real.exp (-(-Real.log q) * (n : ℝ))
    rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
  · rfl

theorem actual_polynomial_reciprocal_errors_have_no_geometric_big_o_bound
    (q power : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ ((fun n : ℕ => (n : ℝ) ^ (-power)) =O[atTop] (fun n : ℕ => q ^ n)) := by
  exact (actual_every_positive_geometric_rate_is_little_o_of_each_polynomial_reciprocal
    q power hq0 hq1).not_isBigO (Eventually.frequently (Eventually.of_forall
      (fun n => (pow_pos hq0 n).ne')))

end SafeLearning.CompleteFoundationsConvergenceRateExamples
