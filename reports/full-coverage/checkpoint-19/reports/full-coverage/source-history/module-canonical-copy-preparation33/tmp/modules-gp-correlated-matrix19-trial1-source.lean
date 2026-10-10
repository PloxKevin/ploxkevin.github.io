import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPCorrelatedMatrix
open CompleteModulesMatrixGP

def sourceGram : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
def sourceQuery (cross : ℝ) : Fin 1 → ℝ := fun _ => cross
def sourceLabels : Fin 1 → ℝ := fun _ => 2

theorem actual_source_singleton_ridge_inverse_is_four_fifths :
    (ridgeMatrix sourceGram (1/4))⁻¹ = (fun _ _ : Fin 1 => (4/5:ℝ)) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.inv_subsingleton,ridgeMatrix,sourceGram,Ring.inverse_eq_inv']

theorem actual_source_full_singleton_matrix_posteriors_are_the_printed_latent_values :
    posteriorMean sourceGram (sourceQuery 1) sourceLabels (1/4)=8/5 ∧
      posteriorVariance sourceGram (sourceQuery 1) 1 (1/4)=1/5 ∧
      posteriorMean sourceGram (sourceQuery (1/2)) sourceLabels (1/4)=4/5 ∧
      posteriorVariance sourceGram (sourceQuery (1/2)) 1 (1/4)=4/5 := by
  norm_num [posteriorMean,posteriorVariance,actual_source_singleton_ridge_inverse_is_four_fifths,
    sourceQuery,sourceLabels,Matrix.mulVec,dotProduct,Fin.sum_univ_one]

end SafeLearning.CompleteModulesGPCorrelatedMatrix
