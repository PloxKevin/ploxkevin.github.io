import SafeLearning.CompleteFoundationsParameterizedConvex
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsParameterizedConvexConsequences
open SafeLearning.CompleteFoundationsParameterizedConvex

theorem actual_smallest_eigenvalue_identity (a : ℝ) :
    min (2+a) (2-a)=2-|a| := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha,min_eq_right (by linarith)]
  · rw [abs_of_neg (lt_of_not_ge ha),min_eq_left (by linarith)];ring

theorem actual_smallest_root_is_attained_and_lower (a : ℝ) :
    (∃ x : E,x≠0 ∧ hessian a x=(2-|a|) • x) ∧
    ∀ lambda : ℝ,(∃ x : E,x≠0 ∧ hessian a x=lambda • x)→2-|a| ≤ lambda := by
  constructor
  · apply (actual_full_hessian_eigenvalues a (2-|a|)).mpr
    by_cases ha : 0 ≤ a
    · right;rw [abs_of_nonneg ha]
    · left;rw [abs_of_neg (lt_of_not_ge ha)];ring
  · intro lambda hl
    rcases (actual_full_hessian_eigenvalues a lambda).mp hl with rfl|rfl
    · linarith [neg_abs_le a]
    · linarith [le_abs_self a]

theorem actual_both_boundary_objectives_are_full_squares (x : E) :
    objective 2 x=(x 0+x 1)^2 ∧ objective (-2) x=(x 0-x 1)^2 := by
  constructor <;> unfold objective <;> ring

theorem actual_both_boundaries_fail_positive_strong_convexity :
    ¬(∃ mu : ℝ,0 < mu ∧ StrongConvexOn Set.univ mu (objective 2)) ∧
    ¬(∃ mu : ℝ,0 < mu ∧ StrongConvexOn Set.univ mu (objective (-2))) := by
  simp only [actual_strong_convex_iff]
  norm_num
end SafeLearning.CompleteFoundationsParameterizedConvexConsequences
