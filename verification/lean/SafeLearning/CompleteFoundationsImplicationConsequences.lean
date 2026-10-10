import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsImplicationConsequences

theorem actual_contrapositive_is_equivalent_to_the_original_implication (P Q : Prop) :
    (P → Q) ↔ (¬ Q → ¬ P) := by
  tauto

theorem actual_empty_domain_check_is_vacuous_and_does_not_constrain_outside :
    (∀ x ∈ (∅ : Set Bool), x = false) ∧
      (true ∉ (∅ : Set Bool) ∧ ¬ (true = false)) := by
  simp

theorem actual_true_control_invariance_can_coexist_with_the_rejected_alternative :
    (∀ x ∈ ({false} : Set Bool), ∃ u ∈ (univ : Set Bool), u ∈ ({false} : Set Bool)) ∧
      (∀ x : Bool, ∃ u : Bool, u ∉ ({false} : Set Bool)) ∧
      ¬ (∃ x ∈ ({false} : Set Bool), ∀ u ∈ (univ : Set Bool), u ∉ ({false} : Set Bool)) := by
  constructor
  · intro x hx
    exact ⟨false, mem_univ _, mem_singleton _⟩
  constructor
  · intro x
    exact ⟨true, by simp⟩
  · rintro ⟨x, hx, hu⟩
    exact hu false (mem_univ _) (mem_singleton _)

theorem actual_finite_pigeonhole_collision
    {Objects Boxes : Type*} [Fintype Objects] [Fintype Boxes]
    (assignment : Objects → Boxes) (hcard : Fintype.card Boxes < Fintype.card Objects) :
    ∃ first second : Objects, first ≠ second ∧ assignment first = assignment second := by
  classical
  have hni := Fintype.not_injective_of_card_lt assignment hcard
  simp only [Function.Injective, not_forall, not_imp] at hni
  obtain ⟨first, second, heq, hne⟩ := hni
  exact ⟨first, second, hne, heq⟩

theorem actual_source_n_plus_one_objects_in_n_boxes (n : ℕ)
    (assignment : Fin (n + 1) → Fin n) :
    ∃ first second : Fin (n + 1), first ≠ second ∧ assignment first = assignment second := by
  apply actual_finite_pigeonhole_collision assignment
  simp

theorem actual_nonzero_norm_half_is_a_positive_violated_tolerance
    {E : Type*} [NormedAddCommGroup E] (x : E) (hx : x ≠ 0) :
    0 < ‖x‖ / 2 ∧ ¬ (‖x‖ ≤ ‖x‖ / 2) := by
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  constructor <;> linarith

end SafeLearning.CompleteFoundationsImplicationConsequences
