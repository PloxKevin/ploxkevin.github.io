import SafeLearning.CompleteModulesScaledGram

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial
namespace SafeLearning.CompleteModulesSLLExamples

def actualSourceWeights : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,1]

def actualFirstMajorizer : Matrix (Fin 2) (Fin 2) ℝ :=
  SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer
    (actualSourceWeightsᵀ*actualSourceWeights) ![1,1]

def actualSecondMajorizer : Matrix (Fin 2) (Fin 2) ℝ :=
  SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer
    (actualSourceWeightsᵀ*actualSourceWeights) ![1,2]

theorem actual_source_gram_matrix : actualSourceWeightsᵀ*actualSourceWeights=
    (!![1,1;1,2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [actualSourceWeights,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_first_scale_majorizer :
    actualFirstMajorizer=Matrix.diagonal (![2,3]:Fin 2 → ℝ) := by
  unfold actualFirstMajorizer
  rw [actual_source_gram_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer,
      SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal,Fin.sum_univ_two]

theorem actual_second_scale_majorizer :
    actualSecondMajorizer=Matrix.diagonal (![3,5/2]:Fin 2 → ℝ) := by
  unfold actualSecondMajorizer
  rw [actual_source_gram_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [SafeLearning.CompleteModulesScaledGram.actualScaledMajorizer,
      SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal,Fin.sum_univ_two]

theorem actual_first_certificate_matrix : actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights=
    (!![1,-1;-1,1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [actual_first_scale_majorizer,actual_source_gram_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

theorem actual_second_certificate_matrix : actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights=
    (!![2,-1;-1,1/2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [actual_second_scale_majorizer,actual_source_gram_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

theorem actual_both_source_certificates_are_positive_semidefinite :
    (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights).PosSemidef ∧
      (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights).PosSemidef := by
  constructor
  · exact SafeLearning.CompleteModulesScaledGram.actual_weighted_gram_matrix_is_bounded_by_source_diagonal
      actualSourceWeights ![1,1] (by intro coordinate; fin_cases coordinate <;> norm_num)
  · exact SafeLearning.CompleteModulesScaledGram.actual_weighted_gram_matrix_is_bounded_by_source_diagonal
      actualSourceWeights ![1,2] (by intro coordinate; fin_cases coordinate <;> norm_num)

theorem actual_first_certificate_characteristic_polynomial :
    (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights).charpoly=X*(X-C 2) := by
  rw [actual_first_certificate_matrix,Matrix.charpoly_fin_two,Matrix.det_fin_two]
  norm_num [Matrix.trace,Fin.sum_univ_two]
  ring

theorem actual_second_certificate_characteristic_polynomial :
    (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights).charpoly=X*(X-C (5/2)) := by
  rw [actual_second_certificate_matrix,Matrix.charpoly_fin_two,Matrix.det_fin_two]
  norm_num [Matrix.trace,Fin.sum_univ_two]
  ring

theorem actual_first_certificate_eigenvalues (eigenvalue : ℝ) :
    eigenvalue ∈ spectrum ℝ (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights) ↔
      eigenvalue=0 ∨ eigenvalue=2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,
    actual_first_certificate_characteristic_polynomial]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_second_certificate_eigenvalues (eigenvalue : ℝ) :
    eigenvalue ∈ spectrum ℝ (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights) ↔
      eigenvalue=0 ∨ eigenvalue=5/2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,
    actual_second_certificate_characteristic_polynomial]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_source_majorizers_are_not_ordered :
    ¬(actualFirstMajorizer-actualSecondMajorizer).PosSemidef ∧
      ¬(actualSecondMajorizer-actualFirstMajorizer).PosSemidef := by
  rw [actual_first_scale_majorizer,actual_second_scale_majorizer]
  constructor
  · intro hpositive
    have h := hpositive.dotProduct_mulVec_nonneg (![1,0]:Fin 2 → ℝ)
    norm_num [Matrix.sub_mulVec,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_two] at h
  · intro hpositive
    have h := hpositive.dotProduct_mulVec_nonneg (![0,1]:Fin 2 → ℝ)
    norm_num [Matrix.sub_mulVec,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_two] at h

end SafeLearning.CompleteModulesSLLExamples
