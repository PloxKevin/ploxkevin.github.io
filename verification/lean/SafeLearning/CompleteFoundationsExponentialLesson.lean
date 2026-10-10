import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsExponentialLesson

theorem actual_exponential_limit_and_two_literal_inequalities (x : ℝ) :
    Tendsto (fun n : ℕ => (1 + x / n)^n) atTop (𝓝 (Real.exp x)) ∧
      1 + x ≤ Real.exp x ∧
      (0 < x → Real.log x ≤ x - 1) := by
  exact ⟨Real.tendsto_one_add_div_pow_exp x,
    by simpa only [add_comm] using Real.add_one_le_exp x,
    fun hx => Real.log_le_sub_one_of_pos hx⟩

def exponentialGap (x : ℝ) : ℝ := Real.exp x - 1 - x

theorem actual_exponential_gap_derivative_and_both_signs (x : ℝ) :
    HasDerivAt exponentialGap (Real.exp x - 1) x ∧
      (x < 0 → Real.exp x - 1 < 0) ∧
      (0 < x → 0 < Real.exp x - 1) ∧
      0 ≤ exponentialGap x ∧ exponentialGap 0 = 0 := by
  refine ⟨?_, fun hx => sub_neg.mpr (Real.exp_lt_one_iff.mpr hx),
    fun hx => sub_pos.mpr (Real.one_lt_exp_iff.mpr hx), ?_, ?_⟩
  · change HasDerivAt (fun z : ℝ => Real.exp z - 1 - z) (Real.exp x - 1) x
    convert ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x) using 1
    funext z
    rfl
  · unfold exponentialGap
    linarith [Real.add_one_le_exp x]
  · simp [exponentialGap]

theorem actual_literal_log_inequality_from_the_exponential_route (x : ℝ) (hx : 0 < x) :
    x ≤ Real.exp (x - 1) ∧ Real.log x ≤ x - 1 := by
  have hb : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
  refine ⟨hb, ?_⟩
  simpa only [Real.log_exp] using Real.log_le_log hx hb

theorem actual_independent_miss_probability_expression_has_exponential_upper_bound
    (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p)^n ≤ Real.exp (-p * n) := by
  have hb : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have h := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hb n
  rw [← Real.exp_nat_mul] at h
  simpa only [mul_comm] using h

theorem actual_discount_log_and_geometric_exponential_bound
    (gamma : ℝ) (hg0 : 0 < gamma) (_hg1 : gamma < 1) (T : ℕ) :
    1 - gamma ≤ Real.log (1 / gamma) ∧
      gamma^T ≤ Real.exp (-(1 - gamma) * T) := by
  have hl := Real.log_le_sub_one_of_pos hg0
  have hlog : 1 - gamma ≤ Real.log (1 / gamma) := by
    rw [one_div, Real.log_inv]
    linarith
  have hp : gamma ≤ Real.exp (-(1 - gamma)) := by
    linarith [Real.add_one_le_exp (-(1 - gamma))]
  have h := pow_le_pow_left₀ hg0.le hp T
  rw [← Real.exp_nat_mul] at h
  refine ⟨hlog, ?_⟩
  simpa only [mul_comm] using h

variable {I : Type*} [Fintype I] [Nonempty I]

def actualMaximum (q : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty q

def actualSoftMaximum (q : I → ℝ) (alpha : ℝ) : ℝ :=
  alpha * Real.log (∑ i, Real.exp (q i / alpha))

theorem actual_finite_maximum_is_attained_and_bounds_every_entry (q : I → ℝ) :
    (∃ j, actualMaximum q = q j) ∧ ∀ i, q i ≤ actualMaximum q := by
  classical
  constructor
  · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty q
    exact ⟨j, hj⟩
  · intro i
    exact Finset.le_sup' q (Finset.mem_univ i)

theorem actual_finite_exponential_sum_has_both_literal_maximum_bounds
    (q : I → ℝ) (alpha : ℝ) (ha : 0 < alpha) :
    Real.exp (actualMaximum q / alpha) ≤ ∑ i, Real.exp (q i / alpha) ∧
      (∑ i, Real.exp (q i / alpha)) ≤
        (Fintype.card I : ℝ) * Real.exp (actualMaximum q / alpha) := by
  classical
  obtain ⟨⟨j, hj⟩, hq⟩ := actual_finite_maximum_is_attained_and_bounds_every_entry q
  constructor
  · rw [hj]
    exact Finset.single_le_sum (fun i _ => (Real.exp_pos (q i / alpha)).le) (Finset.mem_univ j)
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right ha).mpr (hq i)))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum

theorem actual_soft_maximum_is_between_maximum_and_maximum_plus_temperature_log_card
    (q : I → ℝ) (alpha : ℝ) (ha : 0 < alpha) :
    actualMaximum q ≤ actualSoftMaximum q alpha ∧
      actualSoftMaximum q alpha ≤ actualMaximum q + alpha * Real.log (Fintype.card I) := by
  have h := actual_finite_exponential_sum_has_both_literal_maximum_bounds q alpha ha
  have hexp : 0 < Real.exp (actualMaximum q / alpha) := Real.exp_pos _
  have hs : 0 < ∑ i, Real.exp (q i / alpha) := hexp.trans_le h.1
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlo := mul_le_mul_of_nonneg_left (Real.log_le_log hexp h.1) ha.le
  have hup := mul_le_mul_of_nonneg_left (Real.log_le_log hs h.2) ha.le
  rw [Real.log_exp] at hlo
  rw [Real.log_mul hc.ne' hexp.ne', Real.log_exp] at hup
  unfold actualSoftMaximum
  have hid : alpha * (actualMaximum q / alpha) = actualMaximum q := by field_simp
  rw [hid] at hlo
  refine ⟨hlo, ?_⟩
  nlinarith [hup]

theorem actual_soft_maximum_tends_to_actual_maximum_as_temperature_decreases_to_zero
    (q : I → ℝ) :
    Tendsto (actualSoftMaximum q) (𝓝[>] (0 : ℝ)) (𝓝 (actualMaximum q)) := by
  have hb : ∀ᶠ alpha : ℝ in 𝓝[>] 0,
      0 ≤ actualSoftMaximum q alpha - actualMaximum q ∧
      actualSoftMaximum q alpha - actualMaximum q ≤ alpha * Real.log (Fintype.card I) := by
    filter_upwards [self_mem_nhdsWithin] with alpha ha
    have h := actual_soft_maximum_is_between_maximum_and_maximum_plus_temperature_log_card q alpha ha
    constructor <;> linarith
  have hz : Tendsto (fun alpha => actualSoftMaximum q alpha - actualMaximum q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    simpa only [zero_mul, id_eq] using
      ((tendsto_id : Tendsto (fun alpha : ℝ => alpha) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const (Real.log (Fintype.card I))
  simpa only [sub_add_cancel, zero_add] using hz.add_const (actualMaximum q)

end SafeLearning.CompleteFoundationsExponentialLesson
