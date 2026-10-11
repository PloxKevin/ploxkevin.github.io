import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsSubsetContraction
open scoped NNReal

/-- The contraction predicate on a subset uses its inherited distance, without
requiring that the subset form an additive group. -/
theorem actual_subset_norm_contraction_definition {E : Type*} [NormedAddCommGroup E]
    (X : Set E) (g : X→X) (L : ℝ≥0) :
    ContractingWith L g↔
      (L<1 ∧ ∀ x y : X, ‖(g x : E)-(g y : E)‖≤(L:ℝ)*‖(x:E)-(y:E)‖) := by
  simp only [ContractingWith,lipschitzWith_iff_dist_le_mul,Subtype.dist_eq,dist_eq_norm]

end SafeLearning.CompleteFoundationsSubsetContraction
