import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Filter
open scoped Topology

namespace SafeLearning.CompleteModulesSafeOptLogPowerGrowth

/-- Every fixed power of a genuinely shifted/scaled logarithm is sublinear
on actual integer sample counts. This is a limit theorem, not a supplied
information-growth or convergence conclusion. -/
theorem actual_shifted_scaled_log_power_divided_by_integer_time_tends_to_zero
    (a : ℝ) (ha : 0 < a) (power : ℕ) :
    Tendsto (fun T : ℕ => (Real.log (a * ((T : ℝ) + 1))) ^ power / (T : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => (Real.log x) ^ power / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (power : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hu : Tendsto (fun T : ℕ => a * ((T : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have hratio : Tendsto (fun T : ℕ => (a * ((T : ℝ) + 1)) / (T : ℝ)) atTop (𝓝 a) := by
    have h : Tendsto (fun T : ℕ => a * (1 + (T : ℝ)⁻¹)) atTop (𝓝 (a * (1 + 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat)
    simp only [add_zero, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hne : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
    field_simp
  have h := (hbase.comp hu).mul hratio
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hne : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hu0 : a * ((T : ℝ) + 1) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  field_simp

/-- Any genuinely sublinear actual width budget has a finite integer
horizon whose floor allocation is positive and sufficient. The horizon is
chosen as a multiple of the number of windows, and its exact ceiling
condition is also derived; no real-quotient/floor substitution is made. -/
theorem actual_sublinear_width_budget_has_an_exact_positive_rounded_integer_horizon
    (budget : ℕ → ℝ)
    (hbudget : Tendsto (fun T : ℕ => budget T / (T : ℝ)) atTop (𝓝 0))
    (windows : ℕ) (hwindows : 0 < windows) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ horizon : ℕ,
      0 < horizon / windows ∧ budget horizon ≤ ((horizon / windows : ℕ) : ℝ) * epsilon ^ 2 ∧
      windows * max 1 ⌈budget horizon / epsilon ^ 2⌉₊ ≤ horizon := by
  have hw : 0 < (windows : ℝ) := by exact_mod_cast hwindows
  have hsmall : ∀ᶠ T : ℕ in atTop, budget T / (T : ℝ) < epsilon ^ 2 / (windows : ℝ) :=
    (tendsto_order.mp hbudget).2 _ (div_pos (pow_pos hepsilon 2) hw)
  have hmap : Tendsto (fun n : ℕ => windows * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    calc
      b ≤ n := hn
      _ ≤ n + 1 := by omega
      _ ≤ windows * (n + 1) := by nlinarith
  obtain ⟨n, hn⟩ := (hmap.eventually hsmall).exists
  let horizon := windows * (n + 1)
  have hquot : horizon / windows = n + 1 := by
    simp only [horizon, Nat.mul_div_right _ hwindows]
  have htime : 0 < (horizon : ℝ) := by
    exact_mod_cast Nat.mul_pos hwindows (Nat.succ_pos n)
  have hwidth : budget horizon ≤ ((n + 1 : ℕ) : ℝ) * epsilon ^ 2 := by
    have h := (div_lt_iff₀ htime).mp hn
    have he : (epsilon ^ 2 / (windows : ℝ)) * (horizon : ℝ) =
        ((n + 1 : ℕ) : ℝ) * epsilon ^ 2 := by
      dsimp only [horizon]
      rw [Nat.cast_mul]
      field_simp
    rw [he] at h
    exact h.le
  have hceil : ⌈budget horizon / epsilon ^ 2⌉₊ ≤ n + 1 := by
    rw [Nat.ceil_le, div_le_iff₀ (pow_pos hepsilon 2)]
    exact hwidth
  refine ⟨horizon, ?_, ?_, ?_⟩
  · rw [hquot]
    exact Nat.succ_pos n
  · rw [hquot]
    exact hwidth
  · exact Nat.mul_le_mul_left windows (max_le (Nat.succ_le_succ (Nat.zero_le n)) hceil)

end SafeLearning.CompleteModulesSafeOptLogPowerGrowth
