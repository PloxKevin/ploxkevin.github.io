import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsLogicHintNegation

theorem actual_single_bounded_universal_negation_keeps_its_domain
    {X : Type*} (domain : Set X) (predicate : X → Prop) :
    (¬∀ x ∈ domain,predicate x) ↔ ∃ x ∈ domain,¬predicate x := by
  classical
  simp only [not_forall,exists_prop]

theorem actual_bounded_exists_forall_negation_keeps_both_domains
    {X Y : Type*} (first : Set X) (second : Set Y) (relation : X → Y → Prop) :
    (¬∃ x ∈ first,∀ y ∈ second,relation x y) ↔
      ∀ x ∈ first,∃ y ∈ second,¬relation x y := by
  classical
  simp only [not_exists,not_and,not_forall,exists_prop]

theorem actual_source_strict_interval_comparison_is_negated_by_the_self_witness :
    (∀ x ∈ Icc (0:ℝ) 1,∃ y ∈ Icc (0:ℝ) 1,x ≤ y) ∧
      ¬∃ x ∈ Icc (0:ℝ) 1,∀ y ∈ Icc (0:ℝ) 1,x > y := by
  refine ⟨fun x hx => ⟨x,hx,le_rfl⟩,?_⟩
  rintro ⟨x,hx,hy⟩
  exact lt_irrefl x (hy x hx)

end SafeLearning.CompleteFoundationsLogicHintNegation
