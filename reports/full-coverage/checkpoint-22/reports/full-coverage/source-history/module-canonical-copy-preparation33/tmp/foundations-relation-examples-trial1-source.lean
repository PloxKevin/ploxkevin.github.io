import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteFoundationsRelationExamples

def signRelation : Set (ℝ × ℝ) :=
  {p | (0 < p.1 ∧ p.2 = 1) ∨ (p.1 = 0 ∧ |p.2| ≤ 1) ∨ (p.1 < 0 ∧ p.2 = -1)}

theorem actual_source_sign_relation_has_the_exact_three_branches (a b : ℝ) :
    (a,b) ∈ signRelation ↔
      (0 < a ∧ b = 1) ∨ (a = 0 ∧ |b| ≤ 1) ∨ (a < 0 ∧ b = -1) := Iff.rfl

theorem actual_every_sign_relation_output_lies_in_the_vertical_interval
    (a b : ℝ) (hp : (a,b) ∈ signRelation) : -1 ≤ b ∧ b ≤ 1 := by
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [hb]; norm_num
  · exact abs_le.mp hb
  · rw [hb]; norm_num

theorem actual_sign_relation_orders_outputs_at_distinct_increasing_inputs
    (a b c d : ℝ) (hp : (a,b) ∈ signRelation) (hq : (c,d) ∈ signRelation)
    (hac : a < c) : b ≤ d := by
  obtain ⟨hblo,hbhi⟩ := actual_every_sign_relation_output_lies_in_the_vertical_interval a b hp
  obtain ⟨hdlo,hdhi⟩ := actual_every_sign_relation_output_lies_in_the_vertical_interval c d hq
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rcases hq with ⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨hc,hd⟩ <;> linarith

theorem actual_source_sign_relation_is_monotone_in_the_literal_product_sense :
    ∀ p ∈ signRelation, ∀ q ∈ signRelation, 0 ≤ (p.1-q.1)*(p.2-q.2) := by
  rintro ⟨a,b⟩ hp ⟨c,d⟩ hq
  dsimp only
  by_cases hac : a < c
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hac.le)
      (sub_nonpos.mpr (actual_sign_relation_orders_outputs_at_distinct_increasing_inputs a b c d hp hq hac))
  · by_cases hca : c < a
    · exact mul_nonneg (sub_nonneg.mpr hca.le)
        (sub_nonneg.mpr (actual_sign_relation_orders_outputs_at_distinct_increasing_inputs c d a b hq hp hca))
    · have he : a = c := le_antisymm (le_of_not_gt hca) (le_of_not_gt hac)
      simp [he]

theorem actual_sign_relation_has_a_vertical_segment_and_is_not_a_function_graph :
    (∀ b : ℝ, (0,b) ∈ signRelation ↔ |b| ≤ 1) ∧
      ¬ (∃ f : ℝ → ℝ, ∀ a b : ℝ, (a,b) ∈ signRelation ↔ b = f a) := by
  constructor
  · intro b; simp [signRelation]
  · rintro ⟨f,hf⟩
    have hneg : (-1:ℝ)=f 0 := (hf 0 (-1)).mp (by norm_num [signRelation])
    have hpos : (1:ℝ)=f 0 := (hf 0 1).mp (by norm_num [signRelation])
    linarith

def diagonalIncrementRelation (dimension : ℕ) (alpha beta : ℝ)
    (input : Fin dimension → ℝ) : Set (Fin dimension → ℝ) :=
  {output | ∃ D : Matrix (Fin dimension) (Fin dimension) ℝ,
    D.IsDiag ∧ (∀ i, alpha ≤ D i i ∧ D i i ≤ beta) ∧ D.mulVec input = output}

theorem actual_source_diagonal_increment_relation_is_exactly_coordinatewise_slopes
    (dimension : ℕ) (alpha beta : ℝ) (input output : Fin dimension → ℝ) :
    output ∈ diagonalIncrementRelation dimension alpha beta input ↔
      ∃ slopes : Fin dimension → ℝ,
        (∀ i, alpha ≤ slopes i ∧ slopes i ≤ beta) ∧
          (∀ i, output i = slopes i * input i) := by
  constructor
  · rintro ⟨D,hd,hbounds,heq⟩
    refine ⟨fun i => D i i, hbounds, ?_⟩
    intro i
    rw [←heq, ←hd.diagonal_diag]
    simp
  · rintro ⟨slopes,hbounds,heq⟩
    refine ⟨Matrix.diagonal slopes, Matrix.isDiag_diagonal _, ?_, ?_⟩
    · simpa using hbounds
    · ext i; simpa using (heq i).symm

theorem actual_interval_valued_map_membership_has_the_literal_gp_endpoint_formula
    {X : Type*} (mean scale : X → ℝ) (beta : ℝ) (x : X) (value : ℝ) :
    value ∈ Icc (mean x-beta*scale x) (mean x+beta*scale x) ↔
      mean x-beta*scale x ≤ value ∧ value ≤ mean x+beta*scale x := Iff.rfl

theorem actual_successor_sets_are_the_genuine_input_images
    {X U : Type*} (dynamics : X → U → X) (inputs : Set U) (x next : X) :
    next ∈ (dynamics x) '' inputs ↔ ∃ u ∈ inputs, dynamics x u = next := Iff.rfl

end SafeLearning.CompleteFoundationsRelationExamples
