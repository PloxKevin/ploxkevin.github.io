import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsLogicHints

theorem actual_subset_failure_is_an_element_outside_the_other_set
    {X : Type*} (A B : Set X) :
    ¬ B ⊆ A ↔ ∃ x ∈ B, x ∉ A := by
  classical
  simp only [Set.subset_def, not_forall, exists_prop]

theorem actual_union_intersection_and_relative_complement_memberships
    {X : Type*} (ambient A B : Set X) (x : X) :
    (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) ∧
      (x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) ∧
      (x ∈ ambient \ A ↔ x ∈ ambient ∧ x ∉ A) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem actual_dependent_plus_two_witness_and_shared_witness_failure :
    (∀ x : ℝ, ∃ y : ℝ, y = x+2) ∧
      (∀ y : ℝ, y ≠ y+2) ∧ ¬∃ y : ℝ, ∀ x : ℝ, y = x+2 := by
  refine ⟨fun x => ⟨x+2,rfl⟩,fun y => by linarith,?_⟩
  rintro ⟨y,hy⟩
  have h := hy y
  linarith

theorem actual_real_square_nonnegativity_rules_out_every_negative_square
    (x negative : ℝ) (hn : negative < 0) : x^2 ≠ negative := by
  have h := sq_nonneg x
  linarith

theorem actual_bounded_quantifier_negation_keeps_both_domains
    {X U : Type*} (states : Set X) (inputs : Set U) (relation : X → U → Prop) :
    (¬∀ x ∈ states, ∃ u ∈ inputs, relation x u) ↔
      ∃ x ∈ states, ∀ u ∈ inputs, ¬relation x u := by
  classical
  simp only [not_forall, not_exists, not_and, exists_prop]

theorem actual_negation_of_a_strict_real_comparison_includes_equality (x y : ℝ) :
    (¬x > y ↔ x ≤ y) ∧ (x = y → ¬x > y) :=
  ⟨not_lt,fun h => by rw [h]; exact lt_irrefl _⟩

theorem actual_negative_number_is_a_counterexample_to_the_square_converse :
    ((-4:ℝ)^2 > 9) ∧ ¬((-4:ℝ)>3) := by norm_num

theorem actual_every_positive_index_interval_is_contained_in_the_first (n : ℕ)
    (hn : 1 ≤ n) : Icc (-(1/(n:ℝ))) (1/(n:ℝ)) ⊆ Icc (-1:ℝ) 1 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < n := by linarith
  have hb : (1:ℝ)/n ≤ 1 := (div_le_iff₀ hpos).2 (by linarith)
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem actual_archimedean_integer_excludes_any_nonzero_point_from_a_later_interval
    (x : ℝ) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ (1/|x| : ℝ) < n ∧
      (1/(n:ℝ)) < |x| ∧ x ∉ Icc (-(1/(n:ℝ))) (1/(n:ℝ)) := by
  have ha : 0 < |x| := abs_pos.mpr hx
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1:ℝ) (1/|x|))
  have hn1 : (1:ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hni : (1/|x|:ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : (0:ℝ) < n := by linarith
  have hprod : (1:ℝ) < (n:ℝ)*|x| := by
    have h := (div_lt_iff₀ ha).mp hni
    nlinarith
  have hsmall : (1/(n:ℝ)) < |x| := (div_lt_iff₀ hnpos).mpr (by nlinarith)
  refine ⟨n,by exact_mod_cast hn1.le,hni,hsmall,?_⟩
  intro hmem
  have hbound : |x| ≤ 1/(n:ℝ) := abs_le.mpr hmem
  linarith

theorem actual_complement_of_both_interval_conditions_and_excluded_endpoints :
    (∀ x : ℝ, ¬(-1 ≤ x ∧ x ≤ 2) ↔ x < -1 ∨ 2 < x) ∧
      ((-1:ℝ) ∉ (Icc (-1:ℝ) 2)ᶜ) ∧ ((2:ℝ) ∉ (Icc (-1:ℝ) 2)ᶜ) := by
  constructor
  · intro x
    simp only [not_and_or, not_le]
  norm_num

def allowed (state : Fin 3) (input : Fin 2) : Prop :=
  state=2 ∨ (state=0 ∧ input=0) ∨ (state=1 ∧ input=1)

theorem actual_shared_input_must_be_in_every_permitted_input_set
    {X U : Type*} (relation : X → U → Prop) :
    (∃ u, ∀ x, relation x u) ↔ (⋂ x, {u | relation x u}).Nonempty := by
  simp only [Set.nonempty_def, Set.mem_iInter, Set.mem_ofPred_eq]

theorem actual_three_source_states_have_inputs_but_no_input_is_shared :
    (∀ state : Fin 3, ∃ input : Fin 2, allowed state input) ∧
      ¬∃ input : Fin 2, ∀ state : Fin 3, allowed state input := by
  constructor
  · intro state
    fin_cases state
    · exact ⟨0,by simp [allowed]⟩
    · exact ⟨1,by simp [allowed]⟩
    · exact ⟨0,by simp [allowed]⟩
  · rintro ⟨input,hi⟩
    have h0 := hi 0
    have h1 := hi 1
    fin_cases input
    · norm_num [allowed] at h1
    · norm_num [allowed] at h0

theorem actual_cancelling_input_is_uniquely_the_negative_state (x u : ℝ) :
    x+u=0 ↔ u=-x := by constructor <;> intro h <;> linarith

theorem actual_source_cancellation_input_radius_threshold (a : ℝ) :
    (∀ x ∈ Icc (-1:ℝ) 1, ∃ u ∈ Icc (-a) a, x+u=0) ↔ 1 ≤ a := by
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := h 1 (by norm_num)
    have hneg := (actual_cancelling_input_is_uniquely_the_negative_state 1 u).mp he
    rw [hneg] at hu
    linarith [hu.1]
  · intro ha x hx
    refine ⟨-x,⟨by linarith [hx.2],by linarith [hx.1]⟩,by ring⟩

theorem actual_source_opposite_states_rule_out_any_one_shared_cancelling_input :
    ¬∃ u : ℝ, ∀ x ∈ Icc (-1:ℝ) 1, x+u=0 := by
  rintro ⟨u,hu⟩
  have hp := hu 1 (by norm_num)
  have hn := hu (-1) (by norm_num)
  linarith

end SafeLearning.CompleteFoundationsLogicHints
