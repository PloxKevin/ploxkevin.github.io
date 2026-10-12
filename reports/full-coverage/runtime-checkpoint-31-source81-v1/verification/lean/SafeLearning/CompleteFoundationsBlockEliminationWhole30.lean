import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsBlockEliminationWhole30

variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

theorem actual_arbitrary_block_matrix_has_the_literal_three_factor_elimination
    (A : Matrix M M ℝ) (B : Matrix M N ℝ) (C : Matrix N M ℝ) (D : Matrix N N ℝ)
    (hA : IsUnit A) :
    fromBlocks A B C D =
      fromBlocks 1 0 (C*A⁻¹) 1 * fromBlocks A 0 0 (D-C*A⁻¹*B) *
        fromBlocks 1 (A⁻¹*B) 0 1 := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.fromBlocks_eq_of_invertible₁₁ A B C D

theorem actual_arbitrary_block_determinant_is_pivot_times_schur_determinant
    (A : Matrix M M ℝ) (B : Matrix M N ℝ) (C : Matrix N M ℝ) (D : Matrix N N ℝ)
    (hA : IsUnit A) :
    (fromBlocks A B C D).det=A.det*(D-C*A⁻¹*B).det := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.det_fromBlocks₁₁ A B C D

theorem actual_arbitrary_block_matrix_is_invertible_iff_its_schur_complement_is
    (A : Matrix M M ℝ) (B : Matrix M N ℝ) (C : Matrix N M ℝ) (D : Matrix N N ℝ)
    (hA : IsUnit A) :
    IsUnit (fromBlocks A B C D) ↔ IsUnit (D-C*A⁻¹*B) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  simpa only [Matrix.invOf_eq_nonsing_inv] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁ (A := A) (B := B) (C := C) (D := D))

theorem actual_arbitrary_invertible_schur_blocks_have_the_full_printed_inverse
    (A : Matrix M M ℝ) (B : Matrix M N ℝ) (C : Matrix N M ℝ) (D : Matrix N N ℝ)
    (hA : IsUnit A) (hS : IsUnit (D-C*A⁻¹*B)) :
    (fromBlocks A B C D)⁻¹=
      fromBlocks (A⁻¹+A⁻¹*B*(D-C*A⁻¹*B)⁻¹*C*A⁻¹)
        (-(A⁻¹*B*(D-C*A⁻¹*B)⁻¹))
        (-((D-C*A⁻¹*B)⁻¹*C*A⁻¹)) ((D-C*A⁻¹*B)⁻¹) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  have hs : IsUnit (D-C*⅟A*B) := by simpa only [Matrix.invOf_eq_nonsing_inv] using hS
  obtain ⟨iS⟩ := hs.nonempty_invertible
  letI := iS
  letI := Matrix.fromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.invOf_fromBlocks₁₁_eq A B C D

theorem actual_printed_three_by_three_matrix_is_the_actual_partitioned_block_matrix :
    ( (!![2,1,0;1,2,1;0,1,2] : Matrix (Fin 3) (Fin 3) ℝ).submatrix
      (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) finSumFinEquiv ) =
      fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℝ) (!![1,0]) (!![1;0]) (!![2,1;1,2]) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> norm_num [finSumFinEquiv]

theorem actual_printed_three_by_three_elimination_example_has_the_actual_schur_and_determinant :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![2]
    let B : Matrix (Fin 1) (Fin 2) ℝ := !![1,0]
    let C : Matrix (Fin 2) (Fin 1) ℝ := !![1;0]
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,2]
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![1.5,1;1,2]
    A⁻¹=!![1/2] ∧ D-C*A⁻¹*B=S ∧ A.det=2 ∧ S.det=2 ∧
      (fromBlocks A B C D).det=4 := by
  dsimp
  have ha : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹=!![1/2] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_one]
  have hs : (!![2,1;1,2] : Matrix (Fin 2) (Fin 2) ℝ)-(!![1;0] : Matrix (Fin 2) (Fin 1) ℝ)*(!![1/2] : Matrix (Fin 1) (Fin 1) ℝ)*(!![1,0] : Matrix (Fin 1) (Fin 2) ℝ)=!![1.5,1;1,2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_one,Fin.sum_univ_two]
  refine ⟨ha,?_,?_,?_,?_⟩
  · rw [ha]
    exact hs
  · norm_num [Matrix.det_unique]
  · norm_num [Matrix.det_fin_two]
  · have hu : IsUnit (!![2] : Matrix (Fin 1) (Fin 1) ℝ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by norm_num [Matrix.det_unique])
    rw [actual_arbitrary_block_determinant_is_pivot_times_schur_determinant _ _ _ _ hu,ha,hs]
    norm_num [Matrix.det_unique,Matrix.det_fin_two]

end SafeLearning.CompleteFoundationsBlockEliminationWhole30

namespace SafeLearning.CompleteFoundationsBlockEliminationWhole30

theorem actual_printed_three_by_three_full_matrix_has_determinant_four :
    (!![2,1,0;1,2,1;0,1,2] : Matrix (Fin 3) (Fin 3) ℝ).det=4 := by
  have hdet := Matrix.det_submatrix_equiv_self
    (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)
    (!![2,1,0;1,2,1;0,1,2] : Matrix (Fin 3) (Fin 3) ℝ)
  rw [actual_printed_three_by_three_matrix_is_the_actual_partitioned_block_matrix] at hdet
  have hb := actual_printed_three_by_three_elimination_example_has_the_actual_schur_and_determinant
  dsimp only at hb
  exact hdet.symm.trans hb.2.2.2.2

end SafeLearning.CompleteFoundationsBlockEliminationWhole30
