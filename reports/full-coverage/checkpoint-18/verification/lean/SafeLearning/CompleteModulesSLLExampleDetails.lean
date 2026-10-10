import SafeLearning.CompleteModulesSLLExamples

set_option autoImplicit false
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesSLLExampleDetails
open CompleteModulesSLLExamples

theorem actual_first_certificate_determinant_is_zero :
    (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights).det=0 := by
  rw [actual_first_certificate_matrix,Matrix.det_fin_two]
  norm_num

theorem actual_second_certificate_determinant_is_zero :
    (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights).det=0 := by
  rw [actual_second_certificate_matrix,Matrix.det_fin_two]
  norm_num

theorem actual_first_certificate_trace_is_two :
    (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights).trace=2 := by
  rw [actual_first_certificate_matrix]
  norm_num [Matrix.trace,Fin.sum_univ_two]

theorem actual_second_certificate_trace_is_five_halves :
    (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights).trace=5/2 := by
  rw [actual_second_certificate_matrix]
  norm_num [Matrix.trace,Fin.sum_univ_two]

theorem actual_first_certificate_has_actual_nonzero_null_direction :
    (actualFirstMajorizer-actualSourceWeightsᵀ*actualSourceWeights)*ᵥ(![1,1]:Fin 2 → ℝ)=0 ∧
      (![1,1]:Fin 2 → ℝ)≠0 := by
  constructor
  · rw [actual_first_certificate_matrix]
    ext coordinate
    fin_cases coordinate <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · intro h
    have hc := congrFun h 0
    norm_num at hc

theorem actual_second_certificate_has_actual_nonzero_null_direction :
    (actualSecondMajorizer-actualSourceWeightsᵀ*actualSourceWeights)*ᵥ(![1,2]:Fin 2 → ℝ)=0 ∧
      (![1,2]:Fin 2 → ℝ)≠0 := by
  constructor
  · rw [actual_second_certificate_matrix]
    ext coordinate
    fin_cases coordinate <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · intro h
    have hc := congrFun h 0
    norm_num at hc

end SafeLearning.CompleteModulesSLLExampleDetails
