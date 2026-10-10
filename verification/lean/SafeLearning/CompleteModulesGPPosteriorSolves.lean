import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPPosteriorSolves
open CompleteModulesMatrixGP

def sourceGram : Matrix (Fin 2) (Fin 2) ℝ := !![1,1/2;1/2,1]
def sourceLabels : Fin 2 → ℝ := ![1,-1]
def sourceQuery : Fin 2 → ℝ := ![1/2,0]
def sourceQuerySolve : Fin 2 → ℝ := ![3/8,-1/8]
def sourceLatentCovariance : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,1/2,1/2;1/2,1,0;1/2,0,1]

theorem actual_source_ridge_is_the_displayed_matrix :
    ridgeMatrix sourceGram (1/2) = !![3/2,1/2;1/2,3/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ridgeMatrix,sourceGram]

theorem actual_source_ridge_determinant_is_positive_and_unit :
    (ridgeMatrix sourceGram (1/2)).det = 2 ∧
      IsUnit (ridgeMatrix sourceGram (1/2)).det := by
  rw [actual_source_ridge_is_the_displayed_matrix]
  norm_num [Matrix.det_fin_two]

theorem actual_source_label_is_an_actual_eigenvector_and_solve :
    ridgeMatrix sourceGram (1/2) *ᵥ sourceLabels = sourceLabels := by
  rw [actual_source_ridge_is_the_displayed_matrix]
  ext i
  fin_cases i <;> norm_num [sourceLabels,Matrix.mulVec,Fin.sum_univ_two]

theorem actual_source_query_vector_solves_the_actual_regularized_matrix_system :
    ridgeMatrix sourceGram (1/2) *ᵥ sourceQuerySolve = sourceQuery := by
  rw [actual_source_ridge_is_the_displayed_matrix]
  ext i
  fin_cases i <;> norm_num [sourceQuerySolve,sourceQuery,Matrix.mulVec,Fin.sum_univ_two]

theorem actual_source_matrix_solve_iff_the_two_printed_equations (v : Fin 2 → ℝ) :
    (ridgeMatrix sourceGram (1/2) *ᵥ v = sourceQuery) ↔
      (3*v 0+v 1=1 ∧ v 0+3*v 1=0) := by
  rw [actual_source_ridge_is_the_displayed_matrix]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [Matrix.mulVec,Fin.sum_univ_two,sourceQuery,vecHead,vecTail] at h0 h1
    constructor <;> linarith
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec,Fin.sum_univ_two,sourceQuery,vecHead,vecTail] <;> linarith

theorem actual_source_inverse_formulas_equal_the_two_actual_solutions :
    (ridgeMatrix sourceGram (1/2))⁻¹ *ᵥ sourceLabels = sourceLabels ∧
      (ridgeMatrix sourceGram (1/2))⁻¹ *ᵥ sourceQuery = sourceQuerySolve := by
  constructor
  · exact regularized_solve_is_inverse_solution sourceGram sourceLabels sourceLabels (1/2)
      actual_source_ridge_determinant_is_positive_and_unit.2
      actual_source_label_is_an_actual_eigenvector_and_solve
  · exact regularized_solve_is_inverse_solution sourceGram sourceQuery sourceQuerySolve (1/2)
      actual_source_ridge_determinant_is_positive_and_unit.2
      actual_source_query_vector_solves_the_actual_regularized_matrix_system

theorem actual_source_solutions_are_unique (alpha v : Fin 2 → ℝ)
    (ha : ridgeMatrix sourceGram (1/2) *ᵥ alpha = sourceLabels)
    (hv : ridgeMatrix sourceGram (1/2) *ᵥ v = sourceQuery) :
    alpha = sourceLabels ∧ v = sourceQuerySolve := by
  constructor
  · have h := regularized_solve_is_inverse_solution sourceGram sourceLabels alpha (1/2)
      actual_source_ridge_determinant_is_positive_and_unit.2 ha
    exact h.symm.trans actual_source_inverse_formulas_equal_the_two_actual_solutions.1
  · have h := regularized_solve_is_inverse_solution sourceGram sourceQuery v (1/2)
      actual_source_ridge_determinant_is_positive_and_unit.2 hv
    exact h.symm.trans actual_source_inverse_formulas_equal_the_two_actual_solutions.2

theorem actual_source_posterior_matrix_formulas_have_the_printed_values :
    posteriorMean sourceGram sourceQuery sourceLabels (1/2) = 1/2 ∧
      posteriorVariance sourceGram sourceQuery 1 (1/2) = 13/16 ∧
      (13/16 : ℝ) = 8125/10000 := by
  simp only [posteriorMean,posteriorVariance,
    actual_source_inverse_formulas_equal_the_two_actual_solutions.1,
    actual_source_inverse_formulas_equal_the_two_actual_solutions.2]
  norm_num [sourceQuery,sourceLabels,sourceQuerySolve,dotProduct,Fin.sum_univ_two]

theorem actual_source_latent_gram_inverse_is_the_true_inverse :
    sourceGram⁻¹ = !![4/3,-2/3;-2/3,4/3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceGram,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_source_latent_schur_complement_is_positive_two_thirds :
    1-sourceQuery ⬝ᵥ (sourceGram⁻¹ *ᵥ sourceQuery) = 2/3 ∧
      0 < 1-sourceQuery ⬝ᵥ (sourceGram⁻¹ *ᵥ sourceQuery) := by
  rw [actual_source_latent_gram_inverse_is_the_true_inverse]
  norm_num [sourceQuery,dotProduct,Matrix.mulVec,Fin.sum_univ_two]

theorem actual_source_full_latent_covariance_is_positive_definite :
    sourceLatentCovariance.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceLatentCovariance,Matrix.conjTranspose]
  · intro v hv
    have hsome : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have he : star v ⬝ᵥ (sourceLatentCovariance *ᵥ v) =
        (v 0)^2+(v 1)^2+(v 2)^2+v 0*v 1+v 0*v 2 := by
      simp [sourceLatentCovariance,dotProduct,Matrix.mulVec,Fin.sum_univ_three]
      ring
    rw [he]
    have h0 := sq_nonneg (v 0)
    have h1 := sq_nonneg (v 1+v 0/2)
    have h2 := sq_nonneg (v 2+v 0/2)
    by_contra hneg
    have hz : v 0 = 0 := by nlinarith
    rw [hz] at hneg
    rcases hsome with ⟨i,hi⟩
    fin_cases i
    · exact hi hz
    · change v 1 ≠ 0 at hi
      have hp := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (v 2)]
    · change v 2 ≠ 0 at hi
      have hp := sq_pos_of_ne_zero hi
      nlinarith [sq_nonneg (v 1)]

end SafeLearning.CompleteModulesGPPosteriorSolves
