import SafeLearning.CompleteFoundationsRegretRates

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsSparseRegret
open CompleteFoundationsRegretRates

def trialRegret (n : ℕ) : ℝ := (Nat.sqrt (n+1) : ℝ) - Nat.sqrt n
def cumulativeRegret (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, trialRegret k

theorem actual_nonnegative_trial_regrets (n : ℕ) : 0 ≤ trialRegret n := by
  unfold trialRegret
  have h := Nat.sqrt_le_sqrt (show n ≤ n+1 by omega)
  exact sub_nonneg.mpr (by exact_mod_cast h)

theorem actual_trial_sum_is_counting_squares (n : ℕ) :
    cumulativeRegret n = (Nat.sqrt n : ℝ) := by
  induction n with
  | zero => simp [cumulativeRegret]
  | succ n ih =>
    rw [cumulativeRegret, Finset.sum_range_succ]
    change cumulativeRegret n + trialRegret n = _
    rw [ih]
    unfold trialRegret
    ring

theorem actual_cumulative_square_count_upper_bound (n : ℕ) :
    0 ≤ cumulativeRegret n ∧ cumulativeRegret n ≤ Real.sqrt n := by
  rw [actual_trial_sum_is_counting_squares]
  have h := Nat.sqrt_le' n
  have hr : (Nat.sqrt n : ℝ)^2 ≤ n := by exact_mod_cast h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  constructor
  · positivity
  · nlinarith [Real.sqrt_nonneg (n : ℝ),
      (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) by positivity)]

theorem actual_nonnegative_sparse_model_satisfies_source (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ cumulativeRegret n ∧ cumulativeRegret n ≤ sourceRate n := by
  obtain ⟨hl, hu⟩ := actual_cumulative_square_count_upper_bound n
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (1/2 : ℝ) ≤ Real.log n := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnreal
    linarith [Real.log_two_gt_d9]
  refine ⟨hl, hu.trans ?_⟩
  unfold sourceRate
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

theorem actual_square_predecessor_trial_is_one (k : ℕ) :
    trialRegret ((k+1)^2 - 1) = 1 := by
  have hp : 1 ≤ (k+1)^2 := one_le_pow₀ (by omega)
  have he : (k+1)^2 = k^2 + 2*k + 1 := by ring
  have hpred : Nat.sqrt ((k+1)^2 - 1) = k := by
    symm
    apply (Nat.eq_sqrt').mpr
    rw [he]
    constructor <;> omega
  have hsucc : Nat.sqrt (((k+1)^2 - 1)+1) = k+1 := by
    rw [Nat.sub_add_cancel hp, Nat.sqrt_eq']
  simp only [trialRegret, hpred, hsucc, Nat.cast_add, Nat.cast_one]
  ring

theorem actual_nonnegative_trials_do_not_tend_to_zero :
    ¬ Tendsto trialRegret atTop (𝓝 0) := by
  intro h
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h) (1/2) (by norm_num)
  have hn : T ≤ (T+1)^2 - 1 := by
    have hp : 1 ≤ (T+1)^2 := one_le_pow₀ (by omega)
    nlinarith [Nat.sub_add_cancel hp]
  have hb := hT ((T+1)^2 - 1) hn
  rw [actual_square_predecessor_trial_is_one] at hb
  norm_num [Real.dist_eq] at hb

theorem actual_average_vanishes_with_nonvanishing_nonnegative_trials :
    (∀ n, 0 ≤ trialRegret n) ∧
    (∀ n, 2 ≤ n → 0 ≤ cumulativeRegret n ∧ cumulativeRegret n ≤ sourceRate n) ∧
    Tendsto (fun n => cumulativeRegret n / n) atTop (𝓝 0) ∧
      ¬ Tendsto trialRegret atTop (𝓝 0) := by
  exact ⟨actual_nonnegative_trial_regrets, actual_nonnegative_sparse_model_satisfies_source,
    actual_source_average_regret_tends_to_zero cumulativeRegret
      actual_nonnegative_sparse_model_satisfies_source,
    actual_nonnegative_trials_do_not_tend_to_zero⟩

end SafeLearning.CompleteFoundationsSparseRegret
