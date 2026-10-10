import SafeLearning.CompleteModulesMatrixPractice
import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesMatrixPracticeCorollaries
open CompleteModulesMatrixPractice CompleteModulesLipSDP

theorem actual_real_positive_semidefiniteness_is_the_quadratic_condition
    {Index : Type*} [Fintype Index] (matrix : Matrix Index Index ℝ) :
    matrix.PosSemidef ↔ matrix.IsHermitian ∧ ∀ input : Index → ℝ,0 ≤ input ⬝ᵥ(matrix*ᵥinput) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [star_trivial]

theorem actual_source_weighted_energy_decreases_by_actual_euclidean_norm_squared
    (input : Fin 2 → ℝ) :
    (actualPracticeStableNonnormalMatrix*ᵥinput) ⬝ᵥ
      (actualPracticeSteinStorage*ᵥ(actualPracticeStableNonnormalMatrix*ᵥinput))-
        input ⬝ᵥ(actualPracticeSteinStorage*ᵥinput)= -‖WithLp.toLp 2 input‖^2 := by
  rw [squared_norm_of_coordinates,Fin.sum_univ_two]
  exact actual_source_weighted_energy_decreases_by_euclidean_energy input

theorem actual_source_three_stein_entries (first cross last : ℝ) :
    (actualPracticeStableNonnormalMatrixᵀ*actualSymmetricPracticeStorage first cross last*
      actualPracticeStableNonnormalMatrix-actualSymmetricPracticeStorage first cross last) 0 0= -3*first/4 ∧
    (actualPracticeStableNonnormalMatrixᵀ*actualSymmetricPracticeStorage first cross last*
      actualPracticeStableNonnormalMatrix-actualSymmetricPracticeStorage first cross last) 0 1=first-3*cross/4 ∧
    (actualPracticeStableNonnormalMatrixᵀ*actualSymmetricPracticeStorage first cross last*
      actualPracticeStableNonnormalMatrix-actualSymmetricPracticeStorage first cross last) 1 1=4*first+2*cross-3*last/4 := by
  repeat' constructor
  all_goals simp [actualPracticeStableNonnormalMatrix,actualSymmetricPracticeStorage,
    Matrix.mul_apply,Fin.sum_univ_two];ring

end SafeLearning.CompleteModulesMatrixPracticeCorollaries
