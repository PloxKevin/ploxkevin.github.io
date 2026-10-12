import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace SafeLearning.CompleteFoundationsLoewnerOrderWhole30

variable {N : Type*} [Fintype N]

def actualStrictLoewner (A B : Matrix N N ℝ) : Prop := (A-B).PosDef

theorem actual_weak_Loewner_order_is_the_PSD_difference (A B : Matrix N N ℝ) :
    B ≤ A ↔ (A-B).PosSemidef := Matrix.le_iff

theorem actual_symmetric_Loewner_order_is_comparison_in_every_direction
    (A B : Matrix N N ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    B ≤ A ↔ ∀ x : N → ℝ, x ⬝ᵥ B.mulVec x ≤ x ⬝ᵥ A.mulVec x := by
  rw [Matrix.le_iff,Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h x
    have hx := h.2 x
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,sub_nonneg] using hx
  · intro h
    refine ⟨hA.sub hB,?_⟩
    intro x
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub] using sub_nonneg.mpr (h x)

theorem actual_strict_Loewner_notation_is_the_PD_difference (A B : Matrix N N ℝ) :
    actualStrictLoewner A B ↔ (A-B).PosDef := Iff.rfl

theorem actual_strict_symmetric_Loewner_is_strict_comparison_at_every_nonzero_direction
    (A B : Matrix N N ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    actualStrictLoewner A B ↔ ∀ x : N → ℝ, x ≠ 0 → x ⬝ᵥ B.mulVec x < x ⬝ᵥ A.mulVec x := by
  rw [actualStrictLoewner,Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h x hx
    have hq := h.2 hx
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,sub_pos] using hq
  · intro h
    refine ⟨hA.sub hB,?_⟩
    intro x hx
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub] using sub_pos.mpr (h x hx)

theorem actual_Loewner_order_is_reflexive (A : Matrix N N ℝ) : A ≤ A := le_refl A

theorem actual_Loewner_order_is_transitive (A B C : Matrix N N ℝ)
    (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C := le_trans hAB hBC

theorem actual_Loewner_order_is_antisymmetric (A B : Matrix N N ℝ)
    (hAB : A ≤ B) (hBA : B ≤ A) : A = B := le_antisymm hAB hBA

theorem actual_printed_two_diagonal_matrices_are_incomparable :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;0,1]
    ¬ B ≤ A ∧ ¬ A ≤ B := by
  dsimp
  constructor
  · intro h
    have hx := (Matrix.le_iff.mp h).diag_nonneg (i := 1)
    norm_num at hx
  · intro h
    have hx := (Matrix.le_iff.mp h).diag_nonneg (i := 0)
    norm_num at hx

end SafeLearning.CompleteFoundationsLoewnerOrderWhole30
