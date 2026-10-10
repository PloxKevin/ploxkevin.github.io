import SafeLearning.CompleteModulesEllipsoidRoot

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidSpectral
namespace SafeLearning.CompleteModulesEllipsoidOptimum

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def ellipsoidValues (storage matrix : Matrix Index Index ℝ) : Set ℝ :=
  {value | ∃ vector : Index → ℝ,quadraticValue storage vector ≤ 1 ∧ value=quadraticValue matrix vector}

def actualMultipliers (storage matrix : Matrix Index Index ℝ) : Set ℝ :=
  {bound | 0 ≤ bound ∧ (bound • storage-matrix).PosSemidef}

omit [DecidableEq Index] in
theorem actual_matrix_congruence_quadratic_identity
    (matrix map : Matrix Index Index ℝ) (vector : Index → ℝ) :
    quadraticValue matrix (map*ᵥ vector)=quadraticValue (mapᵀ*matrix*map) vector := by
  unfold quadraticValue
  conv_rhs => rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,dotProduct_mulVec,Matrix.vecMul_transpose]

theorem actual_inverse_root_change_of_variable_energy
    (storage : Matrix Index Index ℝ) (hstorage : storage.PosDef) (vector : Index → ℝ) :
    quadraticValue storage (actualInversePositiveSquareRoot storage*ᵥ vector)=vector ⬝ᵥ vector := by
  obtain ⟨_,ht,_,_⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  rw [actual_matrix_congruence_quadratic_identity,ht,
    actual_inverse_positive_square_root_congruence_normalizes_the_energy storage hstorage]
  simp [quadraticValue]

theorem actual_inverse_root_change_of_variable_quadratic
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef) (vector : Index → ℝ) :
    quadraticValue matrix (actualInversePositiveSquareRoot storage*ᵥ vector)=
      quadraticValue (actualNormalizedQuadratic storage matrix) vector := by
  obtain ⟨_,ht,_,_⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  rw [actual_matrix_congruence_quadratic_identity,ht]
  rfl

theorem actual_ellipsoid_value_set_is_exactly_the_normalized_unit_ball_value_set
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef) :
    ellipsoidValues storage matrix=unitBallValues (actualNormalizedQuadratic storage matrix) := by
  obtain ⟨_,_,_,hu⟩ :=
    actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  let := hu.invertible
  ext value
  constructor
  · rintro ⟨vector,henergy,hvalue⟩
    let unitVector := (actualInversePositiveSquareRoot storage)⁻¹*ᵥ vector
    have hv : actualInversePositiveSquareRoot storage*ᵥ unitVector=vector := by
      dsimp [unitVector]
      rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
    have he := actual_inverse_root_change_of_variable_energy storage hstorage unitVector
    have hq := actual_inverse_root_change_of_variable_quadratic storage matrix hstorage unitVector
    rw [hv] at he hq
    exact ⟨unitVector,he ▸ henergy,hvalue.trans hq⟩
  · rintro ⟨vector,henergy,hvalue⟩
    refine ⟨actualInversePositiveSquareRoot storage*ᵥ vector,?_,?_⟩
    · rwa [actual_inverse_root_change_of_variable_energy storage hstorage]
    · rwa [actual_inverse_root_change_of_variable_quadratic storage matrix hstorage]

theorem actual_ellipsoid_quadratic_maximum [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    IsGreatest (ellipsoidValues storage matrix)
      (max 0 (actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
        (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix))) := by
  rw [actual_ellipsoid_value_set_is_exactly_the_normalized_unit_ball_value_set storage matrix hstorage]
  exact actual_unit_ball_quadratic_maximum _ _

theorem actual_smallest_nonnegative_s_procedure_multiplier [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    IsLeast (actualMultipliers storage matrix)
      (max 0 (actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
        (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix))) := by
  constructor
  · exact ⟨le_max_left _ _,
      (actual_ellipsoid_certificate_iff_true_normalized_eigenvalue_bound storage matrix hstorage hmatrix _).2
        (le_max_right _ _)⟩
  · rintro bound ⟨hb,hpsd⟩
    exact max_le hb
      ((actual_ellipsoid_certificate_iff_true_normalized_eigenvalue_bound storage matrix hstorage hmatrix bound).1 hpsd)

theorem actual_ellipsoid_primal_and_multiplier_dual_have_the_same_attained_optimum [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    ∃ value,IsGreatest (ellipsoidValues storage matrix) value ∧
      IsLeast (actualMultipliers storage matrix) value := by
  exact ⟨_,actual_ellipsoid_quadratic_maximum storage matrix hstorage hmatrix,
    actual_smallest_nonnegative_s_procedure_multiplier storage matrix hstorage hmatrix⟩

end SafeLearning.CompleteModulesEllipsoidOptimum
