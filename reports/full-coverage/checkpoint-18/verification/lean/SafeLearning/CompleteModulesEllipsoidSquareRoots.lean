import SafeLearning.CompleteModulesEllipsoidRoot

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidRoot
namespace SafeLearning.CompleteModulesEllipsoidSquareRoots

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def actualPositiveSquareRoot (storage : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  CFC.sqrt storage

theorem actual_positive_square_root_is_psd_and_squares_to_positive_storage
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    (actualPositiveSquareRoot storage).PosSemidef ∧
      actualPositiveSquareRoot storage*actualPositiveSquareRoot storage=storage := by
  exact ⟨(CFC.sqrt_nonneg storage).posSemidef,
    CFC.sqrt_mul_sqrt_self storage hstorage.posSemidef.nonneg⟩

theorem actual_positive_square_root_is_the_inverse_of_the_actual_inverse_square_root
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    actualPositiveSquareRoot storage=(actualInversePositiveSquareRoot storage)⁻¹ := by
  obtain ⟨hr,_,hsq,hu⟩ := actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  let := hstorage.isUnit.invertible
  have hp : (actualInversePositiveSquareRoot storage)⁻¹*(actualInversePositiveSquareRoot storage)⁻¹=storage := by
    rw [←Matrix.mul_inv_rev,hsq,Matrix.inv_inv_of_invertible]
  exact CFC.sqrt_unique hp hr.inv.nonneg

theorem actual_inverse_square_root_is_the_inverse_of_the_actual_positive_square_root
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    actualInversePositiveSquareRoot storage=(actualPositiveSquareRoot storage)⁻¹ := by
  obtain ⟨_,_,_,hu⟩ := actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  let := hu.invertible
  rw [actual_positive_square_root_is_the_inverse_of_the_actual_inverse_square_root storage hstorage,
    Matrix.inv_inv_of_invertible]

theorem actual_source_change_of_variable_is_multiplication_by_the_positive_square_root
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) (vector : Index → ℝ) :
    actualPositiveSquareRoot storage*ᵥ vector=(actualInversePositiveSquareRoot storage)⁻¹*ᵥ vector := by
  rw [actual_positive_square_root_is_the_inverse_of_the_actual_inverse_square_root storage hstorage]

end SafeLearning.CompleteModulesEllipsoidSquareRoots
