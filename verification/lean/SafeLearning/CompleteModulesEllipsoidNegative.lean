import SafeLearning.CompleteModulesEllipsoidOptimum

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidOptimum
namespace SafeLearning.CompleteModulesEllipsoidNegative

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

omit [DecidableEq Index] in
theorem actual_negative_definite_objective_is_strictly_negative_at_nonzero_vectors
    (matrix : Matrix Index Index ℝ) (hnegative : (-matrix).PosDef)
    (vector : Index → ℝ) (hnonzero : vector ≠ 0) : quadraticValue matrix vector < 0 := by
  have h := hnegative.dotProduct_mulVec_pos hnonzero
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at h
  change 0 < -quadraticValue matrix vector at h
  linarith

omit [DecidableEq Index] in
theorem actual_negative_definite_objective_has_zero_ellipsoid_maximum
    (storage matrix : Matrix Index Index ℝ) (hnegative : (-matrix).PosDef) :
    IsGreatest (ellipsoidValues storage matrix) 0 := by
  constructor
  · exact ⟨0,by simp [quadraticValue],by simp [quadraticValue]⟩
  · rintro value ⟨vector,_,rfl⟩
    by_cases hv : vector=0
    · simp [hv,quadraticValue]
    · exact (actual_negative_definite_objective_is_strictly_negative_at_nonzero_vectors matrix hnegative vector hv).le

theorem actual_negative_definiteness_survives_the_inverse_root_congruence
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hnegative : (-matrix).PosDef) : (-actualNormalizedQuadratic storage matrix).PosDef := by
  obtain ⟨_,ht,_,hu⟩ := actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  have h := hu.posDef_star_left_conjugate_iff (x := -matrix)
  have he : star (actualInversePositiveSquareRoot storage)*(-matrix)*actualInversePositiveSquareRoot storage=
      -actualNormalizedQuadratic storage matrix := by
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,ht,
      actualNormalizedQuadratic]
  rw [he] at h
  exact h.mpr hnegative

theorem actual_negative_definite_objective_has_negative_true_largest_normalized_eigenvalue [Nonempty Index]
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) (hnegative : (-matrix).PosDef) :
    actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
      (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix) < 0 := by
  let hm := actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix
  obtain ⟨index,hi⟩ := actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues _ hm
  obtain ⟨_,hq⟩ := actual_true_largest_eigenvector_has_unit_energy_and_its_eigenvalue _ hm index
  have hv : ⇑(hm.eigenvectorBasis index) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hm.eigenvectorBasis.orthonormal.ne_zero index)
  have hn := actual_negative_definiteness_survives_the_inverse_root_congruence storage matrix hstorage hnegative
  have hstrict := actual_negative_definite_objective_is_strictly_negative_at_nonzero_vectors _ hn
    ⇑(hm.eigenvectorBasis index) hv
  rwa [hq,←hi] at hstrict

theorem actual_identity_negative_identity_example_has_largest_eigenvalue_minus_one [Nonempty Index] :
    actualMaximumEigenvalue (-(1 : Matrix Index Index ℝ)) (Matrix.isHermitian_one.neg)=-1 := by
  obtain ⟨index,hi⟩ := actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues
    (-(1 : Matrix Index Index ℝ)) Matrix.isHermitian_one.neg
  obtain ⟨henergy,hq⟩ := actual_true_largest_eigenvector_has_unit_energy_and_its_eigenvalue
    (-(1 : Matrix Index Index ℝ)) Matrix.isHermitian_one.neg index
  rw [hi,←hq]
  simp [quadraticValue,Matrix.neg_mulVec,dotProduct_neg,henergy]

end SafeLearning.CompleteModulesEllipsoidNegative
