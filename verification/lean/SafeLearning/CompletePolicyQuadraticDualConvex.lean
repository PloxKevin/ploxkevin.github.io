import SafeLearning.CompletePolicyQuadraticDual

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyQuadraticDualConvex
open SafeLearning.CompletePolicyQuadraticDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def multiplierDomain : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 ≤ p.2}

theorem actual_multiplier_domain_is_convex : Convex ℝ multiplierDomain := by
  intro p hp q hq a b ha hb hab
  change 0 < a * p.1 + b * q.1 ∧ 0 ≤ a * p.2 + b * q.2
  constructor
  · by_cases ha' : 0 < a
    · exact lt_of_lt_of_le (mul_pos ha' hp.1) (le_add_of_nonneg_right (mul_nonneg hb hq.1.le))
    · have az : a = 0 := le_antisymm (le_of_not_gt ha') ha
      have bo : b = 1 := by linarith
      simpa [az, bo] using hq.1
  · exact add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)

theorem actual_lagrangian_is_affine_in_both_multipliers
    (H : Matrix ι ι ℝ) (g b : ι → ℝ) (c δ : ℝ)
    (p q : ℝ × ℝ) (a z : ℝ) (haz : a + z = 1) (x : ι → ℝ) :
    lagrangian H g b c δ (a * p.1 + z * q.1) (a * p.2 + z * q.2) x =
      a * lagrangian H g b c δ p.1 p.2 x + z * lagrangian H g b c δ q.1 q.2 x := by
  unfold lagrangian
  linear_combination -(g ⬝ᵥ x) * haz

theorem actual_lagrangian_is_bounded_by_its_true_supremum
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (c δ : ℝ)
    (p : ℝ × ℝ) (hp : 0 < p.1) (x : ι → ℝ) :
    lagrangian H g b c δ p.1 p.2 x ≤ actualDual H g b c δ p := by
  rw [show p = (p.1,p.2) from rfl, actual_true_supremum_equals_closed_dual H hH g b c δ p.1 p.2 hp,
    ← actual_attained_closed_dual_value H hH g b c δ p.1 p.2 hp]
  exact actual_global_lagrangian_maximum H hH g b c δ p.1 p.2 hp x

theorem actual_joint_dual_convexity_from_the_true_lagrangian_supremum
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (c δ : ℝ) :
    ConvexOn ℝ multiplierDomain (actualDual H g b c δ) := by
  refine ⟨actual_multiplier_domain_is_convex, ?_⟩
  intro p hp q hq a z ha hz haz
  change actualDual H g b c δ (a * p.1 + z * q.1, a * p.2 + z * q.2) ≤
    a * actualDual H g b c δ p + z * actualDual H g b c δ q
  unfold actualDual at ⊢
  apply csSup_le (range_nonempty _)
  rintro y ⟨x,rfl⟩
  rw [actual_lagrangian_is_affine_in_both_multipliers H g b c δ p q a z haz x]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (actual_lagrangian_is_bounded_by_its_true_supremum H hH g b c δ p hp.1 x) ha)
    (mul_le_mul_of_nonneg_left
      (actual_lagrangian_is_bounded_by_its_true_supremum H hH g b c δ q hq.1 x) hz)

theorem actual_closed_formula_is_jointly_convex
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (c δ : ℝ) :
    ConvexOn ℝ multiplierDomain (fun p => closedDual H g b c δ p.1 p.2) := by
  have h := actual_joint_dual_convexity_from_the_true_lagrangian_supremum H hH g b c δ
  apply h.congr
  intro p hp
  exact actual_true_supremum_equals_closed_dual H hH g b c δ p.1 p.2 hp.1

end SafeLearning.CompletePolicyQuadraticDualConvex
