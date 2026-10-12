import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace SafeLearning.CompleteFoundationsSymmetricHermitianSpectral30

section Generic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

def actualEigenvectorMatrix (A : Matrix n n 𝕜) (hA : A.IsHermitian) : Matrix n n 𝕜 :=
  hA.eigenvectorUnitary

theorem actual_Hermitian_orthonormal_eigenvectors
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    Orthonormal 𝕜 hA.eigenvectorBasis ∧
      ∀ j, A *ᵥ (hA.eigenvectorBasis j : n → 𝕜) =
        hA.eigenvalues j • (hA.eigenvectorBasis j : n → 𝕜) :=
  ⟨hA.eigenvectorBasis.orthonormal,hA.mulVec_eigenvectorBasis⟩

theorem actual_Hermitian_eigenvector_matrix_columns
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) (i j : n) :
    actualEigenvectorMatrix A hA i j = hA.eigenvectorBasis j i := rfl

theorem actual_Hermitian_eigenvector_matrix_is_unitary
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    (actualEigenvectorMatrix A hA).conjTranspose * actualEigenvectorMatrix A hA = 1 ∧
      actualEigenvectorMatrix A hA * (actualEigenvectorMatrix A hA).conjTranspose = 1 := by
  constructor
  · simpa only [actualEigenvectorMatrix,← Matrix.star_eq_conjTranspose,Unitary.coe_star]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [actualEigenvectorMatrix,← Matrix.star_eq_conjTranspose,Unitary.coe_star]
      using Unitary.coe_mul_star_self hA.eigenvectorUnitary

theorem actual_Hermitian_real_diagonal_spectral_reconstruction
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    A = actualEigenvectorMatrix A hA *
      Matrix.diagonal (fun j => (hA.eigenvalues j : 𝕜)) *
      (actualEigenvectorMatrix A hA).conjTranspose := by
  simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
    actualEigenvectorMatrix,Function.comp_def]
    using hA.spectral_theorem

theorem actual_Hermitian_sum_of_eigenvalue_outer_products
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    A = ∑ j, (hA.eigenvalues j : 𝕜) •
      Matrix.vecMulVec (hA.eigenvectorBasis j : n → 𝕜)
        (star (hA.eigenvectorBasis j : n → 𝕜)) := by
  calc
    A = actualEigenvectorMatrix A hA *
      Matrix.diagonal (fun j => (hA.eigenvalues j : 𝕜)) *
      (actualEigenvectorMatrix A hA).conjTranspose :=
        actual_Hermitian_real_diagonal_spectral_reconstruction A hA
    _ = _ := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,
        Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [actual_Hermitian_eigenvector_matrix_columns,actual_Hermitian_eigenvector_matrix_columns]
      ring

theorem actual_Hermitian_entire_spectrum_is_real
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    spectrum 𝕜 A = (fun r : ℝ => (r : 𝕜)) '' Set.range hA.eigenvalues :=
  hA.spectrum_eq_image_range

theorem actual_Hermitian_quadratic_form_is_real
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) (v : n → 𝕜) :
    RCLike.im (star v ⬝ᵥ (A *ᵥ v)) = 0 :=
  hA.im_star_dotProduct_mulVec_self v

end Generic

section Real
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem actual_real_symmetric_orthogonal_diagonalization
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (actualEigenvectorMatrix A hA).transpose * actualEigenvectorMatrix A hA = 1 ∧
    A = actualEigenvectorMatrix A hA * Matrix.diagonal hA.eigenvalues *
      (actualEigenvectorMatrix A hA).transpose ∧
    A = ∑ j, hA.eigenvalues j •
      Matrix.vecMulVec (hA.eigenvectorBasis j : n → ℝ)
        (hA.eigenvectorBasis j : n → ℝ) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using (actual_Hermitian_eigenvector_matrix_is_unitary A hA).1
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,RCLike.ofReal_real_eq_id,id_eq]
      using actual_Hermitian_real_diagonal_spectral_reconstruction A hA
  · simpa only [star_trivial,RCLike.ofReal_real_eq_id,id_eq]
      using actual_Hermitian_sum_of_eigenvalue_outer_products A hA

theorem actual_real_symmetric_complexification_is_Hermitian
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (A.map (algebraMap ℝ ℂ)).IsHermitian := by
  exact hA.map (algebraMap ℝ ℂ) (by intro r; simp)

private theorem actual_complex_energy_positive
    (v : n → ℂ) (hv : v ≠ 0) : 0 < ∑ i, ‖v i‖ ^ 2 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  have hn : v i ≠ 0 := by simpa using hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg ‖v j‖)
    ⟨i,Finset.mem_univ i,sq_pos_of_pos (norm_pos_iff.mpr hn)⟩

theorem actual_complex_Hermitian_eigenvalue_is_real
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (v : n → ℂ) (hv : v ≠ 0)
    (z : ℂ) (hz : A *ᵥ v = z • v) : z.im = 0 := by
  have he : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct,Pi.star_apply,Complex.star_def,Complex.conj_mul',
      Complex.ofReal_sum,Complex.ofReal_pow]
  have h := hA.im_star_dotProduct_mulVec_self v
  rw [hz,dotProduct_smul,smul_eq_mul,he] at h
  change (z * ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)).im = 0 at h
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right (ne_of_gt (actual_complex_energy_positive v hv))

theorem actual_real_matrix_complex_eigenvector_gives_real_eigenvector
    (A : Matrix n n ℝ) (v : n → ℂ) (hv : v ≠ 0) (a : ℝ)
    (h : A.map (algebraMap ℝ ℂ) *ᵥ v = (a : ℂ) • v) :
    ∃ x : n → ℝ, x ≠ 0 ∧ A *ᵥ x = a • x := by
  have hre : A *ᵥ (fun i => (v i).re) = a • (fun i => (v i).re) := by
    ext i
    have hi := congrArg Complex.re (congrFun h i)
    simpa [Matrix.mulVec,dotProduct,Matrix.map_apply] using hi
  have him : A *ᵥ (fun i => (v i).im) = a • (fun i => (v i).im) := by
    ext i
    have hi := congrArg Complex.im (congrFun h i)
    simpa [Matrix.mulVec,dotProduct,Matrix.map_apply] using hi
  by_cases hr : (fun i => (v i).re) = 0
  · refine ⟨(fun i => (v i).im),?_,him⟩
    intro hm
    apply hv
    ext i
    apply Complex.ext
    · simpa using congrFun hr i
    · simpa using congrFun hm i
  · exact ⟨(fun i => (v i).re),hr,hre⟩

theorem actual_real_symmetric_complex_eigenpair_has_real_null_vector
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (v : n → ℂ) (hv : v ≠ 0)
    (z : ℂ) (hz : A.map (algebraMap ℝ ℂ) *ᵥ v = z • v) :
    z.im = 0 ∧ ∃ x : n → ℝ, x ≠ 0 ∧ A *ᵥ x = z.re • x := by
  have hi := actual_complex_Hermitian_eigenvalue_is_real _
    (actual_real_symmetric_complexification_is_Hermitian A hA) v hv z hz
  refine ⟨hi,?_⟩
  have he : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [he] at hz
  exact actual_real_matrix_complex_eigenvector_gives_real_eigenvector A v hv z.re hz

theorem actual_real_symmetric_distinct_eigenvectors_are_orthogonal
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (v w : n → ℝ)
    (a b : ℝ) (hab : a ≠ b) (hv : A *ᵥ v = a • v) (hw : A *ᵥ w = b • w) :
    v ⬝ᵥ w = 0 := by
  have h := hA.star_dotProduct_mulVec_comm v w
  simp only [star_trivial,hv,hw,dotProduct_smul,smul_eq_mul] at h
  rw [dotProduct_comm w v] at h
  have hp : (a-b)*(v ⬝ᵥ w)=0 := by linarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab)

theorem actual_real_symmetric_orthogonal_eigenvector_complement_is_invariant
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (q x : n → ℝ) (a : ℝ)
    (hq : A *ᵥ q = a • q) (hx : q ⬝ᵥ x = 0) : q ⬝ᵥ (A *ᵥ x) = 0 := by
  have h := hA.star_dotProduct_mulVec_comm q x
  simp only [star_trivial,hq,dotProduct_smul,smul_eq_mul] at h
  rw [dotProduct_comm x q,hx,mul_zero] at h
  exact h

end Real

end SafeLearning.CompleteFoundationsSymmetricHermitianSpectral30

namespace SafeLearning.CompleteFoundationsSymmetricHermitianSpectral30
open scoped ComplexOrder

theorem actual_Hermitian_semidefinite_is_nonnegative_complex_form
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    M.PosSemidef ↔ ∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  exact and_iff_right hM

def actualComplexExample : Matrix (Fin 2) (Fin 2) ℂ := !![2,Complex.I;-Complex.I,2]
def actualComplexExampleVector : Fin 2 → ℂ := ![1,Complex.I]

theorem actual_printed_complex_Hermitian_example_and_all_eigenvalues :
    actualComplexExample.IsHermitian ∧
      ∀ z : ℂ, z ∈ spectrum ℂ actualComplexExample ↔ z = 3 ∨ z = 1 := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [actualComplexExample,Complex.star_def]
  · intro z
    have hc : actualComplexExample.charpoly =
        (Polynomial.X-3)*(Polynomial.X-1) := by
      rw [Matrix.charpoly_fin_two]
      norm_num [actualComplexExample,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two,
        Complex.I_sq,Polynomial.C_ofNat] <;> ring
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,hc]
    simp [Polynomial.IsRoot,mul_eq_zero,sub_eq_zero]

theorem actual_printed_complex_vector_quadratic_form :
    star actualComplexExampleVector ⬝ᵥ (actualComplexExample *ᵥ actualComplexExampleVector) = 2 := by
  norm_num [actualComplexExample,actualComplexExampleVector,Matrix.mulVec,dotProduct,
    Fin.sum_univ_two,Complex.star_def,Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

end SafeLearning.CompleteFoundationsSymmetricHermitianSpectral30
