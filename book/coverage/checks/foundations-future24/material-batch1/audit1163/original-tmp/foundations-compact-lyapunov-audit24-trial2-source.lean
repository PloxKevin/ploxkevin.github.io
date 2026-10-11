import Mathlib

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteFoundationsCompactLyapunovAudit24

open Set Filter
open scoped Topology
def sourceMap (x : ℝ) : ℝ := x / (1 + x ^ 2)
def sourceValue (x : ℝ) : ℝ := x ^ 2

def sourceEta (a : ℝ) : ℝ := a * (1 - (1 + a)⁻¹ ^ 2)

theorem actual_source_square_decrement_is_the_printed_eta_expression (x : ℝ) :
    sourceValue (sourceMap x) - sourceValue x = -sourceEta (sourceValue x) := by
  unfold sourceValue sourceMap sourceEta
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem actual_printed_eta_is_positive_at_every_positive_hypothetical_limit
    (a : ℝ) (ha : 0 < a) : 0 < sourceEta a := by
  have hden : 1 < (1 + a) ^ 2 := by nlinarith
  have hinv : (1 + a)⁻¹ ^ 2 < 1 := by
    rw [inv_pow]
    exact inv_lt_one_of_one_lt₀ hden
  exact mul_pos ha (sub_pos.mpr hinv)

theorem actual_printed_eta_is_monotone_on_nonnegative_values
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : sourceEta a ≤ sourceEta b := by
  have hb : 0 ≤ b := ha.trans hab
  have hda : 0 < 1 + a := by linarith
  have hdb : 0 < 1 + b := by linarith
  have hsa : 1 ≤ (1 + a) ^ 2 := by nlinarith
  have hsb : 1 ≤ (1 + b) ^ 2 := by nlinarith
  have hprod : 1 ≤ (1 + a) ^ 2 * (1 + b) ^ 2 := one_le_mul hsa hsb
  have hfactor : 0 ≤ (1 + a) ^ 2 * (1 + b) ^ 2 + a * b - 1 := by
    have hp := mul_nonneg ha hb
    linarith
  have heq : sourceEta b - sourceEta a =
      (b - a) * ((1 + a) ^ 2 * (1 + b) ^ 2 + a * b - 1) /
        ((1 + a) ^ 2 * (1 + b) ^ 2) := by
    unfold sourceEta
    field_simp
    ring
  have hge : 0 ≤ sourceEta b - sourceEta a := by
    rw [heq]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hfactor) (by positivity)
  linarith

theorem actual_square_annulus_decrement_has_exact_maximum_negative_printed_eta
    (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) :
    IsGreatest ((fun x : ℝ => sourceValue (sourceMap x) - sourceValue x) ''
      {x : ℝ | a ≤ sourceValue x ∧ sourceValue x ≤ c}) (-sourceEta a) := by
  have hs : sourceValue (Real.sqrt a) = a := by
    exact Real.sq_sqrt ha.le
  constructor
  · refine ⟨Real.sqrt a, ⟨?_, ?_⟩, ?_⟩
    · rw [hs]
    · simpa only [hs] using hac
    · rw [actual_source_square_decrement_is_the_printed_eta_expression, hs]
  · rintro y ⟨x, hx, rfl⟩
    rw [actual_source_square_decrement_is_the_printed_eta_expression]
    exact neg_le_neg (actual_printed_eta_is_monotone_on_nonnegative_values
      a (sourceValue x) ha.le hx.1)

theorem actual_printed_eta_tends_to_zero_with_the_hypothetical_value_limit :
    Tendsto sourceEta (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt sourceEta 0 := by
    unfold sourceEta
    fun_prop (disch := norm_num)
  simpa [sourceEta] using hc.tendsto

end SafeLearning.CompleteFoundationsCompactLyapunovAudit24
