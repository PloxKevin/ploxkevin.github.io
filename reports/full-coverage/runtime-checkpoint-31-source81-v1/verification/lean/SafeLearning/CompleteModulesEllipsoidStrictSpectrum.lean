import SafeLearning.CompleteModulesEllipsoidRoot

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set Unitary
open scoped MatrixOrder
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
namespace SafeLearning.CompleteModulesEllipsoidStrictSpectrum

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]

theorem actual_true_largest_eigenvalue_strict_bound_iff_every_true_eigenvalue_strictly_bounded
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (bound : ℝ) :
    actualMaximumEigenvalue matrix hsymmetric < bound ↔ ∀ index,hsymmetric.eigenvalues index < bound := by
  constructor
  · intro h index
    exact lt_of_le_of_lt (Finset.le_sup' hsymmetric.eigenvalues (Finset.mem_univ index)) h
  · intro h
    obtain ⟨index,hi⟩ := actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues matrix hsymmetric
    rw [hi]
    exact h index

theorem actual_symmetric_shift_is_pd_iff_strict_true_largest_eigenvalue_bound
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (bound : ℝ) :
    (bound • (1 : Matrix Index Index ℝ)-matrix).PosDef ↔
      actualMaximumEigenvalue matrix hsymmetric < bound := by
  let aut := Unitary.conjStarAlgAut ℝ _ hsymmetric.eigenvectorUnitary
  have hm : matrix=aut (Matrix.diagonal hsymmetric.eigenvalues) := by
    simpa [aut,Function.comp_def] using hsymmetric.spectral_theorem
  have hd : Matrix.diagonal (fun index => bound-hsymmetric.eigenvalues index)=
      bound • (1 : Matrix Index Index ℝ)-Matrix.diagonal hsymmetric.eigenvalues := by
    ext row column
    by_cases he : row=column
    · subst column;simp
    · simp [he]
  have he : bound • (1 : Matrix Index Index ℝ)-matrix=
      aut (Matrix.diagonal (fun index => bound-hsymmetric.eigenvalues index)) := by
    rw [hd,map_sub,map_smul,map_one,←hm]
  rw [he,Unitary.conjStarAlgAut_apply,isUnit_coe.posDef_star_right_conjugate_iff,
    Matrix.posDef_diagonal_iff,
    actual_true_largest_eigenvalue_strict_bound_iff_every_true_eigenvalue_strictly_bounded]
  simp

theorem actual_negative_normalized_largest_eigenvalue_iff_the_source_objective_is_negative_definite
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
      (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix) < 0 ↔
      (-matrix).PosDef := by
  have hs := actual_symmetric_shift_is_pd_iff_strict_true_largest_eigenvalue_bound
    (actualNormalizedQuadratic storage matrix)
    (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix) 0
  simp only [zero_smul,zero_sub] at hs
  obtain ⟨_,ht,_,hu⟩ := actual_inverse_positive_square_root_exists_squares_and_is_invertible storage hstorage
  have hc := hu.posDef_star_left_conjugate_iff (x := -matrix)
  have he : star (actualInversePositiveSquareRoot storage)*(-matrix)*actualInversePositiveSquareRoot storage=
      -actualNormalizedQuadratic storage matrix := by
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,ht,actualNormalizedQuadratic]
  rw [he] at hc
  exact hs.symm.trans hc

theorem actual_zero_clipping_changes_the_true_largest_eigenvalue_iff_negative_definiteness
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.PosDef)
    (hmatrix : matrix.IsHermitian) :
    max 0 (actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
      (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix)) ≠
      actualMaximumEigenvalue (actualNormalizedQuadratic storage matrix)
        (actual_normalized_quadratic_is_symmetric storage matrix hstorage hmatrix) ↔
      (-matrix).PosDef := by
  rw [ne_eq,max_eq_right_iff,not_le]
  exact actual_negative_normalized_largest_eigenvalue_iff_the_source_objective_is_negative_definite storage matrix hstorage hmatrix

end SafeLearning.CompleteModulesEllipsoidStrictSpectrum
