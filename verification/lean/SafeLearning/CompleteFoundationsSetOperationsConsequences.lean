import SafeLearning.CompleteFoundationsSetOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsSetOperationsConsequences

variable {X I : Type*}

theorem actual_indexed_union_and_intersection_membership
    (indices : Set I) (family : I → Set X) (x : X) :
    (x ∈ ⋃ i ∈ indices, family i ↔ ∃ i ∈ indices, x ∈ family i) ∧
      (x ∈ ⋂ i ∈ indices, family i ↔ ∀ i ∈ indices, x ∈ family i) := by
  simp

theorem actual_de_morgan_pointwise_proof_route (family : I → Set X) (x : X) :
    (x ∉ ⋃ i, family i ↔ ∀ i, x ∉ family i) ∧
      (x ∉ ⋂ i, family i ↔ ∃ i, x ∉ family i) ∧
      (family = fun i => ((family i)ᶜ)ᶜ) := by
  classical
  constructor
  · simp
  constructor
  · simp
  · simp

theorem actual_finite_cardinality_counts_the_enumerated_elements
    (A : Set X) (hA : A.Finite) : A.ncard = hA.toFinset.card :=
  Set.ncard_eq_toFinset_card A hA

theorem actual_three_term_summation_has_exact_indices_and_expansion (a : ℝ) :
    Finset.range 3 = ({0, 1, 2} : Finset ℕ) ∧
      (∑ t ∈ Finset.range 3, a ^ t) = a ^ 0 + a ^ 1 + a ^ 2 := by
  constructor
  · decide
  · simp [Finset.sum_range_succ]

theorem actual_source_three_terms_are_one_half_and_quarter :
    (1 / 2 : ℝ) ^ 0 = 1 ∧ (1 / 2 : ℝ) ^ 1 = 1 / 2 ∧
      (1 / 2 : ℝ) ^ 2 = 1 / 4 ∧ (1 + 1 / 2 + 1 / 4 : ℝ) = 7 / 4 := by
  norm_num

end SafeLearning.CompleteFoundationsSetOperationsConsequences
