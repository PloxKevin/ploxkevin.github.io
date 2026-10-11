import SafeLearning.CompleteModulesEllipsoidSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
namespace SafeLearning.CompleteModulesEllipsoidRoot

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def actualInversePositiveSquareRoot (storage : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  CFC.sqrt (storage⁻¹)

theorem actual_inverse_positive_square_root_exists_squares_and_is_invertible
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    (actualInversePositiveSquareRoot storage).PosSemidef ∧
      (actualInversePositiveSquareRoot storage)ᵀ=actualInversePositiveSquareRoot storage ∧
      actualInversePositiveSquareRoot storage*actualInversePositiveSquareRoot storage=storage⁻¹ ∧
      IsUnit (actualInversePositiveSquareRoot storage) := by
  have hi := hstorage.inv
  have hr : (actualInversePositiveSquareRoot storage).PosSemidef :=
    (CFC.sqrt_nonneg (storage⁻¹)).posSemidef
  refine ⟨hr,by simpa using hr.isHermitian.eq,?_,?_⟩
  · exact CFC.sqrt_mul_sqrt_self (storage⁻¹) hi.posSemidef.nonneg
  · exact (CFC.isUnit_sqrt_iff (storage⁻¹) hi.posSemidef.nonneg).2 hi.isUnit

theorem actual_inverse_positive_square_root_congruence_normalizes_the_energy
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    actualInversePositiveSquareRoot storage*storage*actualInversePositiveSquareRoot storage=1 := by
  obtain ⟨_,_,hsq,hu⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  let := hstorage.isUnit.invertible
  have hp : storage=(actualInversePositiveSquareRoot storage)⁻¹*
      (actualInversePositiveSquareRoot storage)⁻¹ := by
    rw [←Matrix.mul_inv_rev,hsq,Matrix.inv_inv_of_invertible]
  conv_lhs => congr; congr; rfl; rw [hp]
  let := hu.invertible
  simp [←Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.inv_mul_of_invertible]

def actualNormalizedQuadratic (storage matrix : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  actualInversePositiveSquareRoot storage*matrix*actualInversePositiveSquareRoot storage

theorem actual_normalized_quadratic_is_symmetric
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) : (actualNormalizedQuadratic storage matrix).IsHermitian := by
  obtain ⟨_,hr,_,_⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  simpa [actualNormalizedQuadratic,Matrix.conjTranspose_eq_transpose_of_trivial,hr] using
    Matrix.isHermitian_conjTranspose_mul_mul (actualInversePositiveSquareRoot storage) hmatrix

theorem actual_ellipsoid_certificate_is_equivalent_to_the_normalized_spectral_shift
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef) (bound : ℝ) :
    (bound • storage-matrix).PosSemidef ↔
      (bound • (1 : Matrix Index Index ℝ)-actualNormalizedQuadratic storage matrix).PosSemidef := by
  obtain ⟨_,hr,_,hu⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  have he : actualInversePositiveSquareRoot storage*(bound • storage-matrix)*
      actualInversePositiveSquareRoot storage=
      bound • (1 : Matrix Index Index ℝ)-actualNormalizedQuadratic storage matrix := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
    rw [actual_inverse_positive_square_root_congruence_normalizes_the_energy storage hstorage]
    rfl
  have hc := hu.posSemidef_star_left_conjugate_iff (x:=bound • storage-matrix)
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,hr,he] using hc.symm

theorem actual_ellipsoid_certificate_iff_true_normalized_eigenvalue_bound [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) (bound : ℝ) :
    (bound • storage-matrix).PosSemidef ↔
      SafeLearning.CompleteModulesEllipsoidSpectral.actualMaximumEigenvalue
        (actualNormalizedQuadratic storage matrix)
        (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix) ≤ bound := by
  rw [actual_ellipsoid_certificate_is_equivalent_to_the_normalized_spectral_shift storage matrix hstorage]
  exact SafeLearning.CompleteModulesEllipsoidSpectral.actual_symmetric_shift_is_psd_iff_bound_exceeds_the_true_largest_eigenvalue
    _ _ _

end SafeLearning.CompleteModulesEllipsoidRoot
