import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteFoundationsDefiniteSchurWhole30
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem actual_bottom_positive_definite_corner_psd_iff
    (A : Matrix I I ℝ) (B : Matrix I J ℝ) (C : Matrix J J ℝ) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᵀ C).PosSemidef ↔ (A - B * C⁻¹ * Bᵀ).PosSemidef := by
  letI := hC.isUnit.invertible
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.fromBlocks₂₂ A B hC

theorem actual_top_positive_definite_corner_psd_iff
    (A : Matrix I I ℝ) (B : Matrix I J ℝ) (C : Matrix J J ℝ) (hA : A.PosDef) :
    (Matrix.fromBlocks A B Bᵀ C).PosSemidef ↔ (C - Bᵀ * A⁻¹ * B).PosSemidef := by
  letI := hA.isUnit.invertible
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.fromBlocks₁₁ B C hA

theorem actual_bottom_positive_definite_corner_strict_iff
    (A : Matrix I I ℝ) (B : Matrix I J ℝ) (C : Matrix J J ℝ) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᵀ C).PosDef ↔ (A - B * C⁻¹ * Bᵀ).PosDef := by
  letI := hC.isUnit.invertible
  have hi : IsUnit (Matrix.fromBlocks A B Bᵀ C) ↔ IsUnit (A - B * C⁻¹ * Bᵀ) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := A) (B := B) (C := Bᵀ) (D := C))
  constructor
  · intro hM
    have hS := (actual_bottom_positive_definite_corner_psd_iff A B C hC).mp hM.posSemidef
    exact hS.posDef_iff_isUnit.mpr (hi.mp hM.isUnit)
  · intro hS
    have hM := (actual_bottom_positive_definite_corner_psd_iff A B C hC).mpr hS.posSemidef
    exact hM.posDef_iff_isUnit.mpr (hi.mpr hS.isUnit)

theorem actual_printed_completed_square
    (A : Matrix I I ℝ) (B : Matrix I J ℝ) (C : Matrix J J ℝ) (hC : C.PosDef)
    (x : I → ℝ) (y : J → ℝ) :
    x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) + y ⬝ᵥ (C *ᵥ y) =
    x ⬝ᵥ ((A - B * C⁻¹ * Bᵀ) *ᵥ x) +
      (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x)) ⬝ᵥ (C *ᵥ (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x))) := by
  letI := hC.isUnit.invertible
  have hs := Matrix.schur_complement_eq₂₂ A B x y hC.isHermitian
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial,
    ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec] at hs
  have hexpand : Sum.elim x y ⬝ᵥ (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim x y) =
    x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) + y ⬝ᵥ (C *ᵥ y) := by
    rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
      dotProduct_add, dotProduct_add, Matrix.dotProduct_transpose_mulVec]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hexpand] at hs
  simpa only [add_comm, add_left_comm, add_assoc] using hs

theorem actual_completed_square_second_term_nonnegative
    (C : Matrix J J ℝ) (hC : C.PosDef) (B : Matrix I J ℝ)
    (x : I → ℝ) (y : J → ℝ) :
    0 ≤ (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x)) ⬝ᵥ (C *ᵥ (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x))) := by
  simpa only [star_trivial] using hC.posSemidef.dotProduct_mulVec_nonneg
    (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x))

theorem actual_completed_square_second_term_vanishes_at_printed_choice
    (C : Matrix J J ℝ) (B : Matrix I J ℝ) (x : I → ℝ) :
    let y := -(C⁻¹ *ᵥ (Bᵀ *ᵥ x))
    (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x)) ⬝ᵥ (C *ᵥ (y + C⁻¹ *ᵥ (Bᵀ *ᵥ x))) = 0 := by
  simp

theorem actual_block_triangular_completion_is_invertible
    (B : Matrix I J ℝ) (C : Matrix J J ℝ) :
    IsUnit (Matrix.fromBlocks (1 : Matrix I I ℝ) 0 (C⁻¹ * Bᵀ) (1 : Matrix J J ℝ)) := by
  exact Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩

theorem actual_definite_schur_is_true_congruence
    (A : Matrix I I ℝ) (B : Matrix I J ℝ) (C : Matrix J J ℝ) (hC : C.PosDef) :
    let T := Matrix.fromBlocks (1 : Matrix I I ℝ) 0 (C⁻¹ * Bᵀ) (1 : Matrix J J ℝ)
    Matrix.fromBlocks A B Bᵀ C =
      Tᵀ * Matrix.fromBlocks (A - B * C⁻¹ * Bᵀ) 0 0 C * T := by
  letI := hC.isUnit.invertible
  have hct : C⁻¹ᵀ = C⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.inv.eq
  have hci : C * (C⁻¹ * Bᵀ) = Bᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have hbi : B * (C⁻¹ * C) = B := by
    rw [Matrix.inv_mul_of_invertible, Matrix.mul_one]
  dsimp
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, hct, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    Matrix.mul_assoc, hci, hbi, sub_add_cancel]
end SafeLearning.CompleteFoundationsDefiniteSchurWhole30
