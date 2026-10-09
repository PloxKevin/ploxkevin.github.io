import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix InnerProductSpace Module
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
namespace SafeLearning.CompleteModulesCholesky

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

def triangularGramFactor (hdim : finrank ℝ E=Fintype.card (Fin n))
    (vectors : Fin n → E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (gramSchmidtOrthonormalBasis hdim vectors).repr (vectors i) j

theorem actual_gram_factor_is_lower_triangular
    (hdim : finrank ℝ E=Fintype.card (Fin n)) (vectors : Fin n → E) :
    (triangularGramFactor hdim vectors).IsLowerTriangular := by
  intro i j hij
  exact gramSchmidtOrthonormalBasis_inv_triangular' hdim vectors hij

theorem actual_gram_factor_product
    (hdim : finrank ℝ E=Fintype.card (Fin n)) (vectors : Fin n → E) :
    triangularGramFactor hdim vectors*(triangularGramFactor hdim vectors)ᵀ=
      Matrix.gram ℝ vectors := by
  ext i j
  have h := (gramSchmidtOrthonormalBasis hdim vectors).repr.inner_map_map (vectors i) (vectors j)
  rw [PiLp.inner_apply] at h
  simpa only [triangularGramFactor,Matrix.mul_apply,Matrix.transpose_apply,Matrix.gram_apply,
    RCLike.inner_apply,conj_trivial,mul_comm] using h

theorem actual_gram_schmidt_diagonal_is_norm (vectors : Fin n → E)
    (hindependent : LinearIndependent ℝ vectors) (i : Fin n) :
    inner ℝ (gramSchmidtNormed ℝ vectors i) (vectors i)=‖gramSchmidt ℝ vectors i‖ := by
  have hnorm : 0 < ‖gramSchmidt ℝ vectors i‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero i hindependent)
  have hinner : inner ℝ (gramSchmidt ℝ vectors i) (vectors i)=‖gramSchmidt ℝ vectors i‖^2 := by
    have hv := gramSchmidt_def'' ℝ vectors i
    have he := congrArg (inner ℝ (gramSchmidt ℝ vectors i)) hv
    rw [he]
    rw [inner_add_right,inner_sum]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    have hsum : (∑ j ∈ Finset.Iio i,
      inner ℝ (gramSchmidt ℝ vectors i)
        ((inner ℝ (gramSchmidt ℝ vectors j) (vectors i)/(↑‖gramSchmidt ℝ vectors j‖ : ℝ)^2) •
          gramSchmidt ℝ vectors j))=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [real_inner_smul_right,gramSchmidt_orthogonal ℝ vectors
        (Finset.mem_Iio.mp hj).ne']
    rw [hsum,add_zero,real_inner_self_eq_norm_sq]
  rw [gramSchmidtNormed,real_inner_smul_left,hinner]
  field_simp
  norm_cast

theorem actual_gram_factor_diagonal_is_positive
    (hdim : finrank ℝ E=Fintype.card (Fin n)) (vectors : Fin n → E)
    (hindependent : LinearIndependent ℝ vectors) (i : Fin n) :
    0 < triangularGramFactor hdim vectors i i := by
  unfold triangularGramFactor
  rw [OrthonormalBasis.repr_apply_apply,gramSchmidtOrthonormalBasis_apply hdim
    (by simpa [gramSchmidtNormed] using gramSchmidt_ne_zero i hindependent),
    actual_gram_schmidt_diagonal_is_norm vectors hindependent i]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero i hindependent)

theorem actual_positive_definite_matrix_has_cholesky
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hpositive : matrix.PosDef) :
    ∃ lower : Matrix (Fin n) (Fin n) ℝ,
      lower.IsLowerTriangular ∧ (∀ i, 0 < lower i i) ∧ matrix=lower*lowerᵀ := by
  obtain ⟨root,hroot⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpositive.posSemidef.nonneg
  let vectors : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (fun j => root j i)
  have hgram : Matrix.gram ℝ vectors=matrix := by
    rw [hroot]
    ext i j
    simp [Matrix.gram_apply,vectors,EuclideanSpace.inner_toLp_toLp,Matrix.mul_apply,
      Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,dotProduct,mul_comm]
  have hindependent : LinearIndependent ℝ vectors :=
    Matrix.linearIndependent_of_posDef_gram (hgram.symm ▸ hpositive)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n))=Fintype.card (Fin n) := by
    simp [finrank_euclideanSpace_fin]
  refine ⟨triangularGramFactor hdim vectors,
    actual_gram_factor_is_lower_triangular hdim vectors,
    actual_gram_factor_diagonal_is_positive hdim vectors hindependent,?_⟩
  rw [actual_gram_factor_product,hgram]

theorem actual_positive_triangular_factor_implies_positive_definite
    (lower : Matrix (Fin n) (Fin n) ℝ) (htriangular : lower.IsLowerTriangular)
    (hdiagonal : ∀ i, 0 < lower i i) : (lower*lowerᵀ).PosDef := by
  have hdet : lower.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular lower htriangular]
    exact ne_of_gt (Finset.prod_pos (fun i hi => hdiagonal i))
  have hunit : IsUnit lower := lower.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  have h := hunit.posDef_star_right_conjugate_iff.mpr (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)
  simpa [Matrix.star_eq_conjTranspose] using h

theorem actual_cholesky_existence_iff_positive_definite
    (matrix : Matrix (Fin n) (Fin n) ℝ) :
    matrix.PosDef ↔ ∃ lower : Matrix (Fin n) (Fin n) ℝ,
      lower.IsLowerTriangular ∧ (∀ i, 0 < lower i i) ∧ matrix=lower*lowerᵀ := by
  refine ⟨actual_positive_definite_matrix_has_cholesky matrix,?_⟩
  rintro ⟨lower,htriangular,hdiagonal,rfl⟩
  exact actual_positive_triangular_factor_implies_positive_definite lower htriangular hdiagonal

theorem actual_exact_cholesky_failure_iff_not_positive_definite
    (matrix : Matrix (Fin n) (Fin n) ℝ) :
    (¬∃ lower : Matrix (Fin n) (Fin n) ℝ,
      lower.IsLowerTriangular ∧ (∀ i, 0 < lower i i) ∧ matrix=lower*lowerᵀ) ↔
        ¬matrix.PosDef :=
  (actual_cholesky_existence_iff_positive_definite matrix).not.symm

theorem actual_positive_definite_leading_principal_minors_are_positive
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hpositive : matrix.PosDef)
    (size : ℕ) (hsize : size ≤ n) :
    0 < (matrix.submatrix (Fin.castLE hsize) (Fin.castLE hsize)).det :=
  (hpositive.submatrix (Fin.castLE_injective hsize)).det_pos

theorem actual_cholesky_factor_reuses_inverse
    (matrix lower : Matrix (Fin n) (Fin n) ℝ) (hfactor : matrix=lower*lowerᵀ) :
    matrix⁻¹=(lower⁻¹)ᵀ*lower⁻¹ := by
  rw [hfactor,Matrix.mul_inv_rev,Matrix.transpose_nonsing_inv]

end SafeLearning.CompleteModulesCholesky
