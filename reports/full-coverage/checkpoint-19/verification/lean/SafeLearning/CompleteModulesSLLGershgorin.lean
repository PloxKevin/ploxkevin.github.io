import SafeLearning.CompleteModulesScaledGram
import Mathlib.LinearAlgebra.Matrix.Gershgorin

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSLLGershgorin

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualSourceSimilarity (matrix : Matrix N N ℝ) (scale : N → ℝ) : Matrix N N ℝ :=
  Matrix.diagonal (fun coordinate => 1/scale coordinate)*matrix*Matrix.diagonal scale

theorem actual_positive_scaling_inverse_product
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    Matrix.diagonal scale*Matrix.diagonal (fun coordinate => 1/scale coordinate)=
      (1 : Matrix N N ℝ) := by
  ext row column
  rw [Matrix.diagonal_mul]
  by_cases he : row=column
  · subst column
    simp [Matrix.diagonal_apply,(hscale row).ne']
  · simp [Matrix.diagonal_apply,he]

theorem actual_similarity_has_same_characteristic_polynomial
    (matrix : Matrix N N ℝ) (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    (actualSourceSimilarity matrix scale).charpoly=matrix.charpoly := by
  unfold actualSourceSimilarity
  rw [Matrix.charpoly_mul_comm,← Matrix.mul_assoc,
    actual_positive_scaling_inverse_product scale hscale,Matrix.one_mul]

theorem actual_real_row_dominant_eigenvalue_is_nonnegative
    (matrix : Matrix N N ℝ)
    (hdominant : ∀ row,(∑ column ∈ Finset.univ.erase row,‖matrix row column‖) ≤ matrix row row)
    (eigenvalue : ℝ) (heigen : eigenvalue ∈ spectrum ℝ matrix) : 0 ≤ eigenvalue := by
  have hs : eigenvalue ∈ spectrum ℝ (Matrix.toLin' matrix) := by
    change eigenvalue ∈ spectrum ℝ (Matrix.toLinAlgEquiv' matrix)
    rw [AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' matrix]
    exact heigen
  have hlin := Module.End.HasEigenvalue.of_mem_spectrum hs
  obtain ⟨row,hrow⟩ := eigenvalue_mem_ball hlin
  rw [mem_closedBall_iff_norm] at hrow
  rw [Real.norm_eq_abs,abs_le] at hrow
  have hd := hdominant row
  linarith

theorem actual_similarity_row_dominance_implies_positive_semidefinite
    (matrix : Matrix N N ℝ) (hhermitian : matrix.IsHermitian)
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (hdominant : ∀ row,
      (∑ column ∈ Finset.univ.erase row,‖actualSourceSimilarity matrix scale row column‖) ≤
        actualSourceSimilarity matrix scale row row) : matrix.PosSemidef := by
  apply hhermitian.posSemidef_iff_eigenvalues_nonneg.mpr
  intro coordinate
  apply actual_real_row_dominant_eigenvalue_is_nonnegative
    (actualSourceSimilarity matrix scale) hdominant
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    actual_similarity_has_same_characteristic_polynomial matrix scale hscale]
  exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp
    (hhermitian.eigenvalues_mem_spectrum_real coordinate)

theorem actual_source_similarity_entry
    (matrix : Matrix N N ℝ) (scale : N → ℝ) (row column : N) :
    actualSourceSimilarity matrix scale row column=matrix row column*scale column/scale row := by
  unfold actualSourceSimilarity
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  ring

theorem actual_source_majorizer_similarity_is_diagonally_dominant
    (symmetric : Matrix N N ℝ) (hdiagonal : ∀ coordinate,0 ≤ symmetric coordinate coordinate)
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) (row : N) :
    (∑ column ∈ Finset.univ.erase row,
      ‖actualSourceSimilarity
        (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric)
          scale row column‖)=
      actualSourceSimilarity
        (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric)
          scale row row := by
  have hoff : ∀ column ∈ Finset.univ.erase row,
      ‖actualSourceSimilarity
        (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric)
          scale row column‖=|symmetric row column| *scale column/scale row := by
    intro column hcolumn
    have hne : row ≠ column := Ne.symm (Finset.mem_erase.mp hcolumn).1
    rw [actual_source_similarity_entry]
    simp only [SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer,
      Matrix.sub_apply,Matrix.diagonal_apply,if_neg hne,zero_sub,Real.norm_eq_abs,
      abs_div,abs_mul,abs_neg,abs_of_pos (hscale column),abs_of_pos (hscale row)]
  rw [Finset.sum_congr rfl hoff,actual_source_similarity_entry]
  simp only [SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer,
    Matrix.sub_apply,Matrix.diagonal_apply,if_pos rfl]
  rw [mul_div_cancel_right₀ _ (hscale row).ne']
  unfold SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ row),abs_of_nonneg (hdiagonal row),
    mul_div_cancel_right₀ _ (hscale row).ne']
  simp

theorem actual_weighted_gram_certificate_has_gershgorin_proof
    {M : Type*} [Fintype M] (weights : Matrix M N ℝ)
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer (weightsᵀ*weights) scale-
      weightsᵀ*weights).PosSemidef := by
  have hh : (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer (weightsᵀ*weights) scale-weightsᵀ*weights).IsHermitian := by
    change (SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer
      (weightsᵀ*weights) scale-weightsᵀ*weights)ᵀ=_
    simp [SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer,Matrix.transpose_mul]
  apply actual_similarity_row_dominance_implies_positive_semidefinite _ hh scale hscale
  intro row
  apply (actual_source_majorizer_similarity_is_diagonally_dominant _ _ scale hscale row).le
  intro coordinate
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

end SafeLearning.CompleteModulesSLLGershgorin
