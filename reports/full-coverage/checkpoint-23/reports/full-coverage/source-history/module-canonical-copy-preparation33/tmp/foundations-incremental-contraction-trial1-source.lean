import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SafeLearning.CompleteFoundationsIncrementalContraction

theorem actual_contraction_iterates_have_the_literal_two_initial_state_bound
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (L : ℝ≥0)
    (hF : LipschitzWith L F) (x y : E) (t : ℕ) :
    ‖F^[t] x - F^[t] y‖ ≤ (L : ℝ) ^ t * ‖x - y‖ := by
  simpa only [dist_eq_norm, NNReal.coe_pow] using (hF.iterate t).dist_le_mul x y

theorem actual_subset_domain_contraction_has_the_ambient_norm_bound
    {E : Type*} [NormedAddCommGroup E] (X : Set E) (F : X → X) (L : ℝ≥0)
    (hF : LipschitzWith L F) (x y : X) (t : ℕ) :
    ‖(F^[t] x : E) - (F^[t] y : E)‖ ≤ (L : ℝ) ^ t * ‖(x : E) - (y : E)‖ := by
  have h := (hF.iterate t).dist_le_mul x y
  simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_pow] using h

theorem actual_every_pair_of_source_recurrences_has_that_incremental_bound
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (L : ℝ≥0)
    (hF : LipschitzWith L F) (x y : ℕ → E)
    (hx : ∀ t : ℕ, x (t + 1) = F (x t))
    (hy : ∀ t : ℕ, y (t + 1) = F (y t)) :
    ∀ t : ℕ, ‖x t - y t‖ ≤ (L : ℝ) ^ t * ‖x 0 - y 0‖ := by
  have hxi : ∀ t : ℕ, x t = F^[t] (x 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hx, Function.iterate_succ_apply', ih]
  have hyi : ∀ t : ℕ, y t = F^[t] (y 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hy, Function.iterate_succ_apply', ih]
  intro t
  rw [hxi t, hyi t]
  exact actual_contraction_iterates_have_the_literal_two_initial_state_bound F L hF _ _ t

theorem actual_two_contraction_trajectories_approach_each_other
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (L : ℝ≥0)
    (hF : LipschitzWith L F) (hL : (L : ℝ) < 1) (x y : E) :
    Tendsto (fun t : ℕ => ‖F^[t] x - F^[t] y‖) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one L.coe_nonneg hL).mul_const ‖x - y‖
  apply squeeze_zero (fun _ => norm_nonneg _)
    (actual_contraction_iterates_have_the_literal_two_initial_state_bound F L hF x y)
  simpa using ht

theorem actual_initial_epsilon_bound_is_preserved_at_every_time
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (L : ℝ≥0)
    (hF : LipschitzWith L F) (hL : (L : ℝ) ≤ 1) (x y : E)
    (epsilon : ℝ) (hinitial : ‖x - y‖ < epsilon) :
    ∀ t : ℕ, ‖F^[t] x - F^[t] y‖ < epsilon := by
  intro t
  have hpower : (L : ℝ) ^ t ≤ 1 := pow_le_one₀ L.coe_nonneg hL
  have h := actual_contraction_iterates_have_the_literal_two_initial_state_bound F L hF x y t
  have hb := mul_le_mul_of_nonneg_right hpower (norm_nonneg (x - y))
  exact (h.trans (by simpa using hb)).trans_lt hinitial

end SafeLearning.CompleteFoundationsIncrementalContraction
