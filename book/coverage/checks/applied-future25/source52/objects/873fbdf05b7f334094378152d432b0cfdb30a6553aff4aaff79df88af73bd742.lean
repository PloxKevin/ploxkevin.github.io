import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set Unitary
namespace SafeLearning.CompleteModulesPseudoinverse

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def actualSpectralAut (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :=
  Unitary.conjStarAlgAut ℝ _ hsymmetric.eigenvectorUnitary

def actualPseudoinverse (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    Matrix Index Index ℝ :=
  actualSpectralAut matrix hsymmetric (Matrix.diagonal (fun index =>
    (hsymmetric.eigenvalues index)⁻¹))

theorem actual_matrix_is_its_true_spectral_conjugate
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix=actualSpectralAut matrix hsymmetric (Matrix.diagonal hsymmetric.eigenvalues) := by
  simpa [actualSpectralAut,Function.comp_def] using hsymmetric.spectral_theorem

theorem actual_pseudoinverse_is_symmetric
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    (actualPseudoinverse matrix hsymmetric).IsHermitian := by
  unfold actualPseudoinverse actualSpectralAut
  rw [Unitary.conjStarAlgAut_apply]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ (Matrix.isHermitian_diagonal _)

theorem actual_pseudoinverse_satisfies_both_generalized_inverse_equations
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric*matrix=matrix ∧
    actualPseudoinverse matrix hsymmetric*matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric := by
  let aut:=actualSpectralAut matrix hsymmetric
  let values:=hsymmetric.eigenvalues
  have hm : matrix=aut (Matrix.diagonal values) :=
    actual_matrix_is_its_true_spectral_conjugate matrix hsymmetric
  have hp : actualPseudoinverse matrix hsymmetric=
      aut (Matrix.diagonal (fun index => (values index)⁻¹)) := rfl
  rw [hp,hm]
  simp only [←map_mul,Matrix.diagonal_mul_diagonal]
  constructor
  · congr 2
    funext index
    by_cases hv : values index=0
    · simp [hv]
    · field_simp
  · congr 2
    funext index
    by_cases hv : values index=0
    · simp [hv]
    · field_simp

theorem actual_pseudoinverse_commutes_with_the_matrix
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric*matrix := by
  let aut:=actualSpectralAut matrix hsymmetric
  let values:=hsymmetric.eigenvalues
  have hm : matrix=aut (Matrix.diagonal values) :=
    actual_matrix_is_its_true_spectral_conjugate matrix hsymmetric
  have hp : actualPseudoinverse matrix hsymmetric=
      aut (Matrix.diagonal (fun index => (values index)⁻¹)) := rfl
  rw [hp,hm]
  simp only [←map_mul,Matrix.diagonal_mul_diagonal]
  congr 2
  funext index
  exact mul_comm _ _

theorem actual_pseudoinverse_satisfies_all_four_moore_penrose_equations
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*actualPseudoinverse matrix hsymmetric*matrix=matrix ∧
    actualPseudoinverse matrix hsymmetric*matrix*actualPseudoinverse matrix hsymmetric=
      actualPseudoinverse matrix hsymmetric ∧
    (matrix*actualPseudoinverse matrix hsymmetric)ᵀ=
      matrix*actualPseudoinverse matrix hsymmetric ∧
    (actualPseudoinverse matrix hsymmetric*matrix)ᵀ=
      actualPseudoinverse matrix hsymmetric*matrix := by
  obtain ⟨hm,hp⟩:=actual_pseudoinverse_satisfies_both_generalized_inverse_equations matrix hsymmetric
  have hmt : matrixᵀ=matrix := by simpa using hsymmetric.eq
  have hpt : (actualPseudoinverse matrix hsymmetric)ᵀ=actualPseudoinverse matrix hsymmetric := by
    simpa using (actual_pseudoinverse_is_symmetric matrix hsymmetric).eq
  refine ⟨hm,hp,?_,?_⟩
  · rw [Matrix.transpose_mul,hmt,hpt]
    exact (actual_pseudoinverse_commutes_with_the_matrix matrix hsymmetric).symm
  · rw [Matrix.transpose_mul,hmt,hpt]
    exact actual_pseudoinverse_commutes_with_the_matrix matrix hsymmetric

theorem actual_zero_matrix_pseudoinverse_is_zero :
    actualPseudoinverse (0 : Matrix Index Index ℝ) (Matrix.isHermitian_zero)=0 := by
  have h:=actual_pseudoinverse_satisfies_both_generalized_inverse_equations
    (0 : Matrix Index Index ℝ) Matrix.isHermitian_zero
  simpa using h.2.symm

theorem actual_pseudoinverse_null_projection_has_image_in_the_actual_kernel
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix*(1-actualPseudoinverse matrix hsymmetric*matrix)=0 := by
  rw [Matrix.mul_sub,Matrix.mul_one,←Matrix.mul_assoc,
    (actual_pseudoinverse_satisfies_both_generalized_inverse_equations matrix hsymmetric).1,
    sub_self]

end SafeLearning.CompleteModulesPseudoinverse
