import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsConvergenceRates

theorem actual_one_step_geometric_error_bound_gives_every_natural_prefix_bound
    (error : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ n, error (n + 1) ≤ q * error n) :
    ∀ n, error n ≤ q ^ n * error 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      error (n + 1) ≤ q * error n := hstep n
      _ ≤ q * (q ^ n * error 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * error 0 := by rw [pow_succ]; ring

theorem actual_nonnegative_geometrically_bounded_errors_converge_to_zero
    (error : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hnonnegative : ∀ n, 0 ≤ error n)
    (hstep : ∀ n, error (n + 1) ≤ q * error n) :
    Tendsto error atTop (𝓝 0) := by
  have hp := actual_one_step_geometric_error_bound_gives_every_natural_prefix_bound
    error q hq0 hstep
  have ht : Tendsto (fun n : ℕ => q ^ n * error 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (error 0)
  exact squeeze_zero hnonnegative hp ht

theorem actual_positive_geometric_certificate_is_equivalent_to_the_printed_logarithmic_cutoff
    (q initial epsilon : ℝ) (n : ℕ) (hq0 : 0 < q) (hq1 : q < 1)
    (hi : 0 < initial) (he : 0 < epsilon) :
    q ^ n * initial ≤ epsilon ↔
      Real.log (initial / epsilon) / Real.log (1 / q) ≤ (n : ℝ) := by
  have hlogq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hlog : 0 < Real.log (1 / q) := by
    rw [one_div, Real.log_inv]
    linarith
  rw [← Real.log_le_log_iff (mul_pos (pow_pos hq0 n) hi) he,
    Real.log_mul (pow_ne_zero n hq0.ne') hi.ne', Real.log_pow,
    Real.log_div hi.ne' he.ne', div_le_iff₀ hlog, one_div, Real.log_inv]
  constructor <;> intro h <;> nlinarith

theorem actual_source_half_rate_first_tolerance_index_is_twenty :
    (1 / 2 : ℝ) ^ 20 ≤ 1 / 1000000 ∧
      1 / 1000000 < (1 / 2 : ℝ) ^ 19 ∧
      ∀ n : ℕ, (1 / 2 : ℝ) ^ n ≤ 1 / 1000000 ↔ 20 ≤ n := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro n
  constructor
  · intro hn
    by_contra h
    have hsmall : n ≤ 19 := by omega
    have hp : (1 / 2 : ℝ) ^ 19 ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsmall
    have hbad : 1 / 1000000 < (1 / 2 : ℝ) ^ 19 := by norm_num
    linarith
  · intro hn
    calc
      (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 20 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ ≤ 1 / 1000000 := by norm_num

theorem actual_positive_square_root_error_cutoff_is_exactly_the_inverse_square
    (index epsilon : ℝ) (hi : 0 < index) (he : 0 < epsilon) :
    1 / Real.sqrt index ≤ epsilon ↔ 1 / epsilon ^ 2 ≤ index := by
  have hs : 0 < Real.sqrt index := Real.sqrt_pos.2 hi
  rw [div_le_iff₀ hs, div_le_iff₀ (sq_pos_of_pos he)]
  have hsquare := Real.sq_sqrt hi.le
  constructor
  · intro h
    nlinarith [sq_nonneg (epsilon * Real.sqrt index - 1)]
  · intro h
    have hp : 0 < epsilon * Real.sqrt index := mul_pos he hs
    nlinarith [sq_nonneg (epsilon * Real.sqrt index - 1)]

theorem actual_source_square_root_tolerance_requires_one_trillion_indices
    (n : ℕ) (hn : 0 < n) :
    1 / Real.sqrt (n : ℝ) ≤ 1 / 1000000 ↔ 1000000000000 ≤ n := by
  rw [actual_positive_square_root_error_cutoff_is_exactly_the_inverse_square
    (n : ℝ) (1 / 1000000) (by exact_mod_cast hn) (by norm_num)]
  norm_num

end SafeLearning.CompleteFoundationsConvergenceRates
