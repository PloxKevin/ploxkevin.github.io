import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteBarrierIntroMaterial24

theorem actual_square_minus_one_safe_set (x : ℝ) :
    0 ≤ x ^ 2 - 1 ↔ 1 ≤ |x| := by
  have ha : 0 ≤ |x| := abs_nonneg x
  have hs : |x| ^ 2 = x ^ 2 := sq_abs x
  constructor <;> intro h <;> nlinarith

theorem actual_square_minus_one_chain_rule
    (trajectory : ℝ → ℝ) (t u : ℝ)
    (h : HasDerivAt trajectory u t) :
    HasDerivAt (fun s => trajectory s ^ 2 - 1) (2 * trajectory t * u) t := by
  convert (h.pow 2).sub_const 1 using 1
  ring

theorem actual_nominal_minus_two_projection_to_minus_one :
    (-1 : ℝ) ≥ -1 ∧
    ∀ u : ℝ, -1 ≤ u →
      dist (-1 : ℝ) (-2) ≤ dist u (-2) ∧
      (dist u (-2) = dist (-1 : ℝ) (-2) ↔ u = -1) := by
  refine ⟨le_rfl, ?_⟩
  intro u hu
  have hnonneg : 0 ≤ u - (-2) := by linarith
  have hone : dist (-1 : ℝ) (-2) = 1 := by norm_num [Real.dist_eq]
  rw [hone, Real.dist_eq, abs_of_nonneg hnonneg]
  constructor
  · linarith
  · constructor <;> intro h <;> linarith

theorem actual_square_barrier_value_tracks_safety (x : ℝ) :
    x ∈ {point : ℝ | 0 ≤ point ^ 2 - 1} ↔ |x| ≥ 1 :=
  actual_square_minus_one_safe_set x

end SafeLearning.CompleteBarrierIntroMaterial24
