import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsRegretRates

def sourceRate (n : ℕ) : ℝ := 5 * Real.sqrt n * Real.log n

theorem actual_logarithmic_average_limit :
    Tendsto (fun n : ℕ => 5 * Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
  have hr : Tendsto (fun t : ℝ => 5 * Real.log t / Real.sqrt t) atTop (𝓝 0) := by
    simpa [Real.sqrt_eq_rpow, mul_div_assoc] using h.const_mul 5
  exact hr.comp tendsto_natCast_atTop_atTop

theorem actual_cumulative_bound_implies_average_bound
    (R : ℕ → ℝ) (hR : ∀ n, 2 ≤ n → 0 ≤ R n ∧ R n ≤ sourceRate n)
    (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ R n / n ∧ R n / n ≤ 5 * Real.log n / Real.sqrt n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs := Real.mul_self_sqrt hpos.le
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have he : sourceRate n / n = 5 * Real.log n / Real.sqrt n := by
    unfold sourceRate
    field_simp
    nlinarith [congrArg (fun z : ℝ => z * Real.log n) hs]
  exact ⟨div_nonneg (hR n hn).1 hpos.le, (div_le_div_of_nonneg_right (hR n hn).2 hpos.le).trans_eq he⟩

theorem actual_source_average_regret_tends_to_zero
    (R : ℕ → ℝ) (hR : ∀ n, 2 ≤ n → 0 ≤ R n ∧ R n ≤ sourceRate n) :
    Tendsto (fun n => R n / n) atTop (𝓝 0) := by
  have hb : ∀ᶠ n in atTop, 0 ≤ R n / n ∧ R n / n ≤ 5 * Real.log n / Real.sqrt n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact actual_cumulative_bound_implies_average_bound R hR n hn
  exact squeeze_zero' (hb.mono fun n hn => hn.1) (hb.mono fun n hn => hn.2)
    actual_logarithmic_average_limit

theorem actual_log_ten_thousand_rounding :
    |Real.log (10000 : ℝ) - 921034/100000| < 1/200000 := by
  have he : Real.log (10000 : ℝ) = 4 * (Real.log 2 + Real.log 5) := by
    rw [show (10000 : ℝ) = (2 * 5)^4 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [he, abs_lt]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    Real.log_five_gt_d9, Real.log_five_lt_d9]

theorem actual_finite_budget_upper_bound
    (R : ℕ → ℝ) (hR : ∀ n, 2 ≤ n → 0 ≤ R n ∧ R n ≤ sourceRate n) :
    Real.sqrt (10000 : ℝ) = 100 ∧ R 10000 / 10000 ≤ 46052/100000 := by
  have hs : Real.sqrt (10000 : ℝ) = 100 := by norm_num
  have hb := (actual_cumulative_bound_implies_average_bound R hR 10000 (by norm_num)).2
  norm_num only [Nat.cast_ofNat] at hb
  obtain ⟨hl, hu⟩ := abs_lt.mp actual_log_ten_thousand_rounding
  exact ⟨hs, by linarith⟩

theorem actual_sqrt_rate_little_o :
    IsLittleO atTop (fun n : ℕ => Real.sqrt n) (fun n => (n : ℝ)) := by
  have hr : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hs := Real.mul_self_sqrt ht.le
    have hn : Real.sqrt t ≠ 0 := by positivity
    field_simp
    nlinarith
  apply isLittleO_of_tendsto
  · intro n hn
    simpa only [hn, Real.sqrt_zero]
  · exact hr.comp tendsto_natCast_atTop_atTop

theorem actual_sqrt_product_and_ratio (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt n * Real.sqrt n = (n : ℝ) ∧
      Real.sqrt n * Real.sqrt n / n = 1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Real.mul_self_sqrt hp.le]
  exact ⟨rfl, div_self hp.ne'⟩

theorem actual_product_is_not_little_o :
    ¬ IsLittleO atTop (fun n : ℕ => Real.sqrt n * Real.sqrt n) (fun n => (n : ℝ)) := by
  intro h
  have ho := h.tendsto_div_nhds_zero
  have he : Tendsto (fun n : ℕ => Real.sqrt n * Real.sqrt n / n) atTop (𝓝 1) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (actual_sqrt_product_and_ratio n hn).2.symm
  have hbad := tendsto_nhds_unique ho he
  norm_num at hbad

def trialRegret (n : ℕ) : ℝ := (-1)^n
def cumulativeRegret (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, trialRegret k

theorem actual_trial_cumulative_identity (n : ℕ) :
    cumulativeRegret n = (1 - (-1 : ℝ)^n)/2 := by
  induction n with
  | zero => simp [cumulativeRegret]
  | succ n ih =>
    rw [cumulativeRegret, Finset.sum_range_succ]
    change cumulativeRegret n + trialRegret n = _
    rw [ih]
    simp only [trialRegret, pow_succ]
    ring

theorem actual_cumulative_nonnegative_and_bounded (n : ℕ) :
    0 ≤ cumulativeRegret n ∧ cumulativeRegret n ≤ 1 := by
  have ha : |(-1 : ℝ)^n| = 1 := by simp only [abs_pow, abs_neg, abs_one, one_pow]
  have hb : -1 ≤ (-1 : ℝ)^n ∧ (-1 : ℝ)^n ≤ 1 := abs_le.mp ha.le
  rw [actual_trial_cumulative_identity]
  constructor <;> linarith

theorem actual_trial_model_satisfies_source_bound (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ cumulativeRegret n ∧ cumulativeRegret n ≤ sourceRate n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (1/2 : ℝ) ≤ Real.log n := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnreal
    linarith [Real.log_two_gt_d9]
  have hroot : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by linarith)
  obtain ⟨hl, hu⟩ := actual_cumulative_nonnegative_and_bounded n
  refine ⟨hl, hu.trans ?_⟩
  unfold sourceRate
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (sub_nonneg.mpr hlog)]

theorem actual_individual_trial_regrets_need_not_tend_to_zero :
    ¬ Tendsto trialRegret atTop (𝓝 0) := by
  intro h
  have hn := h.norm
  have he : (fun n => ‖trialRegret n‖) = (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    simp [trialRegret, Real.norm_eq_abs, abs_pow]
  rw [he] at hn
  have hb := tendsto_nhds_unique hn (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at hb

end SafeLearning.CompleteFoundationsRegretRates
