import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsImplicationLesson

theorem actual_implication_fails_exactly_at_true_p_and_false_q (P Q : Prop) :
    (¬ (P → Q)) ↔ P ∧ ¬ Q := by
  tauto

theorem actual_implication_is_vacuous_when_the_premise_is_false (P Q : Prop)
    (hP : ¬ P) : P → Q := by
  exact fun hp => False.elim (hP hp)

theorem actual_disjunction_is_the_negated_alternative_guard (P Q : Prop) :
    (P ∨ Q) ↔ (¬ Q → P) := by
  tauto

theorem actual_source_strict_square_implication_and_false_converse :
    (∀ x : ℝ, 2 < x → 4 < x ^ 2) ∧
      (4 < (-3 : ℝ) ^ 2 ∧ ¬ (2 < (-3 : ℝ))) ∧
      (∀ x : ℝ, x ^ 2 ≤ 4 → x ≤ 2) := by
  refine ⟨?_, by norm_num, ?_⟩
  · intro x hx
    nlinarith [sq_nonneg (x - 2)]
  · intro x hx
    by_contra hn
    have hp : 2 < x := lt_of_not_ge hn
    nlinarith [sq_nonneg (x - 2)]

theorem actual_source_decrease_and_successor_disjunction_iff_guard
    {X : Type*} (decrease value radius : ℝ) (successor : X) (box : Set X) :
    ((decrease ≤ 0 ∧ successor ∈ box) ∨ radius ≤ value) ↔
      (value < radius → decrease ≤ 0 ∧ successor ∈ box) := by
  constructor
  · intro h hv
    rcases h with h | h
    · exact h
    · linarith
  · intro h
    by_cases hv : value < radius
    · exact Or.inl (h hv)
    · exact Or.inr (le_of_not_gt hv)

theorem actual_all_state_source_guard_equivalence
    {X : Type*} (box : Set X) (decrease value : X → ℝ)
    (successor : X → X) (radius : ℝ) :
    (∀ x ∈ box, (decrease x ≤ 0 ∧ successor x ∈ box) ∨ radius ≤ value x) ↔
      (∀ x ∈ box, value x < radius → decrease x ≤ 0 ∧ successor x ∈ box) := by
  constructor
  · intro h x hx
    exact (actual_source_decrease_and_successor_disjunction_iff_guard
      (decrease x) (value x) radius (successor x) box).mp (h x hx)
  · intro h x hx
    exact (actual_source_decrease_and_successor_disjunction_iff_guard
      (decrease x) (value x) radius (successor x) box).mpr (h x hx)

theorem actual_negation_of_control_invariance_has_the_source_quantifier_order
    {X U : Type*} (safe : Set X) (inputs : Set U) (successor : X → U → X) :
    (¬ ∀ x ∈ safe, ∃ u ∈ inputs, successor x u ∈ safe) ↔
      ∃ x ∈ safe, ∀ u ∈ inputs, successor x u ∉ safe := by
  classical
  simp only [not_forall, not_exists, not_and, exists_prop]

theorem actual_norm_bounded_by_every_positive_tolerance_forces_zero
    {E : Type*} [NormedAddCommGroup E] (x : E)
    (h : ∀ tolerance : ℝ, 0 < tolerance → ‖x‖ ≤ tolerance) : x = 0 := by
  by_contra hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb := h (‖x‖ / 2) (by positivity)
  linarith

theorem actual_norm_equality_iff_all_positive_tolerance_bounds
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    x = y ↔ ∀ tolerance : ℝ, 0 < tolerance → ‖x - y‖ ≤ tolerance := by
  constructor
  · rintro rfl tolerance ht
    simpa using ht.le
  · intro h
    exact sub_eq_zero.mp (actual_norm_bounded_by_every_positive_tolerance_forces_zero (x-y) h)

end SafeLearning.CompleteFoundationsImplicationLesson
