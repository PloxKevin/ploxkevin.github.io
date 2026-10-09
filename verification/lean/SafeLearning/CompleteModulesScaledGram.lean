import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesScaledGram

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualMajorizerDiagonal (symmetric : Matrix N N ℝ) (scale : N → ℝ) (row : N) : ℝ :=
  ∑ column, |symmetric row column| *scale column/scale row

def actualScaledMajorizer (symmetric : Matrix N N ℝ) (scale : N → ℝ) : Matrix N N ℝ :=
  Matrix.diagonal (actualMajorizerDiagonal symmetric scale)

theorem actual_scaled_young_inequality
    (left right firstScale secondScale : ℝ) (hfirst : 0<firstScale) (hsecond : 0<secondScale) :
    2*|left| *|right|≤(secondScale/firstScale)*left^2+(firstScale/secondScale)*right^2 := by
  have hproduct : 0<firstScale*secondScale := mul_pos hfirst hsecond
  have he : firstScale*secondScale*((secondScale/firstScale)*left^2+
      (firstScale/secondScale)*right^2-2*|left| *|right|)=
      (secondScale*|left|-firstScale*|right|)^2 := by
    field_simp
    ring_nf
    simp only [sq_abs]
  have hn : 0≤firstScale*secondScale*((secondScale/firstScale)*left^2+
      (firstScale/secondScale)*right^2-2*|left| *|right|) := by
    rw [he]
    positivity
  have hd := (mul_nonneg_iff_of_pos_left hproduct).mp hn
  linarith

theorem actual_scaled_symmetric_pair_bound
    (entry left right firstScale secondScale : ℝ)
    (hfirst : 0<firstScale) (hsecond : 0<secondScale) :
    2*entry*left*right≤|entry| *((secondScale/firstScale)*left^2+
      (firstScale/secondScale)*right^2) := by
  have hy := actual_scaled_young_inequality left right firstScale secondScale hfirst hsecond
  calc
    _ = 2*(entry*left*right) := by ring
    _ ≤ 2*|entry*left*right| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ = |entry| *(2*|left| *|right|) := by simp only [abs_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (abs_nonneg entry)

theorem actual_symmetric_quadratic_is_bounded_by_scaled_majorizer
    (symmetric : Matrix N N ℝ) (hsymmetric : symmetricᵀ=symmetric)
    (scale vector : N → ℝ) (hscale : ∀ coordinate, 0<scale coordinate) :
    vector ⬝ᵥ(symmetric*ᵥvector)≤
      ∑ coordinate, actualMajorizerDiagonal symmetric scale coordinate*vector coordinate^2 := by
  have hpair := Finset.sum_le_sum (fun row (_ : row ∈ Finset.univ) =>
    Finset.sum_le_sum (fun column (_ : column ∈ Finset.univ) =>
      actual_scaled_symmetric_pair_bound (symmetric row column) (vector row) (vector column)
        (scale row) (scale column) (hscale row) (hscale column)))
  have hswap : (∑ row, ∑ column,
      |symmetric row column| *((scale row/scale column)*vector column^2))=
      ∑ row, ∑ column, |symmetric row column| *((scale column/scale row)*vector row^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro row hrow
    apply Finset.sum_congr rfl
    intro column hcolumn
    have he := congrArg (fun matrix : Matrix N N ℝ => matrix row column) hsymmetric
    simp only [Matrix.transpose_apply] at he
    rw [he]
  have hright : (∑ row, ∑ column,
      |symmetric row column| *((scale column/scale row)*vector row^2+
        (scale row/scale column)*vector column^2))=
      2*(∑ row, actualMajorizerDiagonal symmetric scale row*vector row^2) := by
    simp_rw [mul_add,Finset.sum_add_distrib]
    rw [hswap]
    unfold actualMajorizerDiagonal
    simp_rw [Finset.sum_mul]
    have he : (∑ row, ∑ column, |symmetric row column| *((scale column/scale row)*vector row^2))=
        ∑ row, ∑ column, (|symmetric row column| *scale column/scale row)*vector row^2 := by
      apply Finset.sum_congr rfl
      intro row hrow
      apply Finset.sum_congr rfl
      intro column hcolumn
      ring
    rw [he]
    ring
  have hleft : (∑ row, ∑ column, 2*symmetric row column*vector row*vector column)=
      2*(vector ⬝ᵥ(symmetric*ᵥvector)) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row hrow
    apply Finset.sum_congr rfl
    intro column hcolumn
    ring
  rw [hleft,hright] at hpair
  linarith

theorem actual_scaled_majorizer_difference_is_positive_semidefinite
    (symmetric : Matrix N N ℝ) (hsymmetric : symmetricᵀ=symmetric)
    (scale : N → ℝ) (hscale : ∀ coordinate, 0<scale coordinate) :
    (actualScaledMajorizer symmetric scale-symmetric).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (actualScaledMajorizer symmetric scale-symmetric)ᵀ=
      actualScaledMajorizer symmetric scale-symmetric
    simp [actualScaledMajorizer,Matrix.transpose_sub,hsymmetric]
  · intro vector
    have hb := actual_symmetric_quadratic_is_bounded_by_scaled_majorizer
      symmetric hsymmetric scale vector hscale
    have hdiagonal : actualScaledMajorizer symmetric scale*ᵥvector=
        fun coordinate => actualMajorizerDiagonal symmetric scale coordinate*vector coordinate := by
      ext coordinate
      simp [actualScaledMajorizer,Matrix.mulVec,dotProduct,Matrix.diagonal_apply]
    simpa [Matrix.sub_mulVec,hdiagonal,dotProduct,
      Finset.sum_sub_distrib,mul_sub,pow_two,mul_comm,mul_left_comm,mul_assoc]
      using sub_nonneg.mpr hb

theorem actual_weighted_gram_matrix_is_bounded_by_source_diagonal
    {M : Type*} [Fintype M] (weights : Matrix M N ℝ)
    (scale : N → ℝ) (hscale : ∀ coordinate, 0<scale coordinate) :
    (actualScaledMajorizer (weightsᵀ*weights) scale-weightsᵀ*weights).PosSemidef := by
  apply actual_scaled_majorizer_difference_is_positive_semidefinite _ _ scale hscale
  simp [Matrix.transpose_mul]

end SafeLearning.CompleteModulesScaledGram
