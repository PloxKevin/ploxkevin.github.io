import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsConvexKink

theorem actual_absolute_value_is_convex : ConvexOn ℝ Set.univ (abs : ℝ→ℝ) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb _
  change |a*x+b*y| ≤ a*|x|+b*|y|
  calc
    |a*x+b*y| ≤ |a*x|+|b*y| := abs_add_le _ _
    _=a*|x|+b*|y| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]

def IsSubgradientAt (f : ℝ→ℝ) (s x : ℝ) : Prop :=
  ∀ y : ℝ,f x+s*(y-x) ≤ f y

theorem actual_zero_subgradient_iff_global_minimum (f : ℝ→ℝ) (x : ℝ) :
    IsSubgradientAt f 0 x ↔ ∀ y : ℝ,f x ≤ f y := by
  simp [IsSubgradientAt]
end SafeLearning.CompleteFoundationsConvexKink
