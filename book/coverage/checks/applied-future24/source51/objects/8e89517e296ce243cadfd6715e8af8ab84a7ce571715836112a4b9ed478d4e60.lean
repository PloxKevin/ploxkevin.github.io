import SafeLearning.CompleteFoundationsTelescopingModels
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeSuiArithmetic

open CompleteFoundationsTelescopingModels

/-- The source allocation starts at t=2. Natural subtraction is converted
only under that actual index condition. -/
theorem actual_source_failure_share_reciprocal_at_round_two_or_later
    (delta : ℝ) (t : ℕ) (ht : 2 ≤ t) :
    (failureShare delta (t - 2))⁻¹ = (t : ℝ) / delta * ((t : ℝ) - 1) := by
  have hcast : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by
    rw [Nat.cast_sub ht]
    norm_num
  unfold failureShare
  rw [hcast, inv_div]
  ring

/-- The exact source reciprocal allocation logarithm is at most twice the
displayed log(t/delta), without replacing natural-index subtraction. -/
theorem actual_source_failure_allocation_log_is_bounded_by_twice_the_source_log
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1)
    (t : ℕ) (ht : 2 ≤ t) :
    Real.log ((failureShare delta (t - 2))⁻¹) ≤ 2 * Real.log ((t : ℝ) / delta) := by
  have hreal : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hpositive : 0 < (t : ℝ) := by linarith
  have hratio : (t : ℝ) ≤ (t : ℝ) / delta :=
    (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hpositive.le hdone.le)
  have hlast : (t : ℝ) - 1 ≤ (t : ℝ) / delta :=
    (sub_le_self _ zero_le_one).trans hratio
  have hbound : (failureShare delta (t - 2))⁻¹ ≤ ((t : ℝ) / delta) ^ 2 := by
    rw [actual_source_failure_share_reciprocal_at_round_two_or_later delta t ht, pow_two]
    exact mul_le_mul_of_nonneg_left hlast (div_nonneg hpositive.le hd.le)
  have hshare : 0 < (failureShare delta (t - 2))⁻¹ := by
    unfold failureShare
    positivity
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hshare hbound

/-- The lower bound log2>=2/3 is derived from the analytic inequality
2x/(x+2)<=log(1+x), rather than a supplied numerical estimate. -/
theorem actual_source_round_log_is_at_least_two_thirds
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1)
    (t : ℕ) (ht : 2 ≤ t) :
    (2 / 3 : ℝ) ≤ Real.log ((t : ℝ) / delta) := by
  have hreal : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hpositive : 0 ≤ (t : ℝ) := by linarith
  have hratio : (t : ℝ) ≤ (t : ℝ) / delta :=
    (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hpositive hdone.le)
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    convert Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num) using 1 <;> norm_num
  exact htwo.trans (Real.log_le_log (by norm_num) (hreal.trans hratio))

private theorem actual_cubic_is_at_least_four_ninths_times_its_argument
    (l : ℝ) (hl : (2 / 3 : ℝ) ≤ l) : (4 / 9 : ℝ) * l ≤ l ^ 3 := by
  have hnonnegative : 0 ≤ l := by linarith
  have hsquare : (4 / 9 : ℝ) ≤ l ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsquare hnonnegative]

/-- The first deterministic intermediate coefficient fits within the
literal source constant300 on the actual logarithm range. -/
theorem actual_four_plus_sixteen_log_is_bounded_by_three_hundred_log_cubed
    (l : ℝ) (hl : (2 / 3 : ℝ) ≤ l) : 4 + 16 * l ≤ 300 * l ^ 3 := by
  have hcubic := actual_cubic_is_at_least_four_ninths_times_its_argument l hl
  linarith

/-- The second deterministic intermediate coefficient fits within the
same literal source constant300. -/
theorem actual_forty_times_one_plus_log_is_bounded_by_three_hundred_log_cubed
    (l : ℝ) (hl : (2 / 3 : ℝ) ≤ l) : 40 * (1 + l) ≤ 300 * l ^ 3 := by
  have hcubic := actual_cubic_is_at_least_four_ninths_times_its_argument l hl
  linarith

/-- Both arithmetic estimates specialize to the exact source logarithm. -/
theorem actual_source_round_log_satisfies_both_three_hundred_cubic_bounds
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1)
    (t : ℕ) (ht : 2 ≤ t) :
    4 + 16 * Real.log ((t : ℝ) / delta) ≤ 300 * (Real.log ((t : ℝ) / delta)) ^ 3 ∧
      40 * (1 + Real.log ((t : ℝ) / delta)) ≤ 300 * (Real.log ((t : ℝ) / delta)) ^ 3 := by
  have hlog := actual_source_round_log_is_at_least_two_thirds delta hd hdone t ht
  exact ⟨actual_four_plus_sixteen_log_is_bounded_by_three_hundred_log_cubed _ hlog,
    actual_forty_times_one_plus_log_is_bounded_by_three_hundred_log_cubed _ hlog⟩

/-- Nonnegative squared-norm and information terms give a nonnegative
literal source beta expression. This is an arithmetic implication only. -/
theorem actual_source_two_B_plus_three_hundred_information_log_cubed_is_nonnegative
    (B Gamma delta : ℝ) (hB : 0 ≤ B) (hGamma : 0 ≤ Gamma)
    (hd : 0 < delta) (hdone : delta < 1) (t : ℕ) (ht : 2 ≤ t) :
    0 ≤ 2 * B + 300 * Gamma * (Real.log ((t : ℝ) / delta)) ^ 3 := by
  have hlog := actual_source_round_log_is_at_least_two_thirds delta hd hdone t ht
  have hnonnegative : 0 ≤ Real.log ((t : ℝ) / delta) := by linarith
  positivity

end SafeLearning.CompleteModulesLandscapeSuiArithmetic
