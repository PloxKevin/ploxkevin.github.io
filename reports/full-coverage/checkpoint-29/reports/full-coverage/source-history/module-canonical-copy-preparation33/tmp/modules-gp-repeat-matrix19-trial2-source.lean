import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPRepeatMatrix
open CompleteModulesMatrixGP

def sourceOnes (n : ℕ) : Fin n → ℝ := fun _ => 1
def sourceGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
def sourceSolution (n : ℕ) : Fin n → ℝ := fun _ => 1/((n : ℝ)+1)

theorem actual_repeated_unit_prior_gram_is_the_literal_outer_product (n : ℕ) :
    sourceGram n = Matrix.vecMulVec (sourceOnes n) (sourceOnes n) := by
  ext i j
  simp [sourceGram, sourceOnes, Matrix.vecMulVec]

theorem actual_repeated_unit_prior_gram_square_is_dimension_times_the_gram (n : ℕ) :
    sourceGram n * sourceGram n = (n : ℝ) • sourceGram n := by
  ext i j
  simp [sourceGram, Matrix.mul_apply]

theorem actual_literal_regularized_repeated_gram_has_the_true_inverse (n : ℕ) :
    (ridgeMatrix (sourceGram n) 1)⁻¹ =
      1 - (1/((n : ℝ)+1)) • sourceGram n := by
  apply Matrix.inv_eq_left_inv
  simp only [ridgeMatrix, one_smul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    actual_repeated_unit_prior_gram_square_is_dimension_times_the_gram]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, sourceGram]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem actual_source_ones_vector_is_mapped_to_dimension_times_itself (n : ℕ) :
    sourceGram n *ᵥ sourceOnes n = (n : ℝ) • sourceOnes n := by
  ext i
  simp [sourceGram, sourceOnes, Matrix.mulVec, dotProduct]

theorem actual_printed_vector_solves_the_true_regularized_repeated_matrix_system (n : ℕ) :
    ridgeMatrix (sourceGram n) 1 *ᵥ sourceSolution n = sourceOnes n := by
  simp only [ridgeMatrix, one_smul, Matrix.add_mulVec, Matrix.one_mulVec]
  ext i
  simp [sourceGram, sourceSolution, sourceOnes, Matrix.mulVec, dotProduct]

theorem actual_inverse_applied_to_the_repeated_query_is_the_printed_solution (n : ℕ) :
    (ridgeMatrix (sourceGram n) 1)⁻¹ *ᵥ sourceOnes n = sourceSolution n := by
  rw [actual_literal_regularized_repeated_gram_has_the_true_inverse,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    actual_source_ones_vector_is_mapped_to_dimension_times_itself]
  ext i
  simp [sourceOnes, sourceSolution]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem actual_posterior_matrix_variance_at_the_repeated_input_is_one_over_n_plus_one (n : ℕ) :
    posteriorVariance (sourceGram n) (sourceOnes n) 1 1 = 1/((n : ℝ)+1) := by
  rw [posteriorVariance, actual_inverse_applied_to_the_repeated_query_is_the_printed_solution]
  simp [dotProduct, sourceOnes, sourceSolution]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

end SafeLearning.CompleteModulesGPRepeatMatrix
