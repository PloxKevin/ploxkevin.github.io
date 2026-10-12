import SafeLearning.CompleteModulesCholesky
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open Matrix MeasureTheory
namespace SafeLearning.CompleteFoundationsDeterminantLog30

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The literal multiplicative determinant rule, including singular and empty matrices. -/
theorem actual_determinant_of_product (A B : Matrix I I ℝ) :
    (A * B).det = A.det * B.det := Matrix.det_mul A B

/-- The literal transpose rule needs no symmetry or invertibility premise. -/
theorem actual_determinant_of_transpose (A : Matrix I I ℝ) :
    A.transpose.det = A.det := Matrix.det_transpose A

/-- For a real matrix, all complex characteristic roots are counted with multiplicity.
This is the full eigenvalue-product rule even when the real matrix is not symmetric. -/
theorem actual_real_determinant_is_product_of_all_complex_eigenvalues
    (A : Matrix I I ℝ) :
    (A.det : ℂ) = (A.map (algebraMap ℝ ℂ)).charpoly.roots.prod := by
  have hm : (A.det : ℂ) = (A.map (algebraMap ℝ ℂ)).det := by
    simpa only [RingHom.mapMatrix_apply, Complex.coe_algebraMap] using (algebraMap ℝ ℂ).map_det A
  exact hm.trans (Matrix.det_eq_prod_roots_charpoly _)

/-- The true Lebesgue-volume image formula applies also to singular matrices, arbitrary
sets and dimension zero; its factor is the absolute determinant. -/
theorem actual_absolute_determinant_is_the_volume_factor
    (A : Matrix I I ℝ) (s : Set (I → ℝ)) :
    volume ((fun x => A *ᵥ x) '' s) = ENNReal.ofReal |A.det| * volume s := by
  have hf : (Matrix.toLin' A : (I → ℝ) → (I → ℝ)) = (fun x => A *ᵥ x) := by
    funext x
    exact Matrix.toLin'_apply A x
  have h := (volume : Measure (I → ℝ)).addHaar_image_linearMap (Matrix.toLin' A) s
  rw [hf, LinearMap.det_toLin'] at h
  exact h

/-- Matrix scalar multiplication scales determinant by dimension, for every real scalar. -/
theorem actual_determinant_of_scalar_multiple (c : ℝ) (A : Matrix I I ℝ) :
    (c • A).det = c ^ Fintype.card I * A.det := Matrix.det_smul A c

/-- Positivity is derived from actual positive definiteness. -/
theorem actual_positive_definite_determinant_is_positive
    (P : Matrix I I ℝ) (hP : P.PosDef) : 0 < P.det := hP.det_pos

/-- The logarithm of the actual positive determinant is the sum of logs of its true
positive eigenvalues, including the empty sum/product in dimension zero. -/
theorem actual_positive_definite_log_determinant_is_sum_of_eigenvalue_logs
    (P : Matrix I I ℝ) (hP : P.PosDef) :
    Real.log P.det = ∑ i, Real.log (hP.isHermitian.eigenvalues i) := by
  rw [hP.isHermitian.det_eq_prod_eigenvalues]
  exact Real.log_prod (fun i _ => ne_of_gt (hP.eigenvalues_pos i))

/-- Every positive-diagonal lower Cholesky factor gives the printed twice-log-diagonal
formula. The positive diagonal is the standard Cholesky convention. -/
theorem actual_log_determinant_from_an_actual_positive_cholesky_factor
    {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ)
    (htri : L.IsLowerTriangular) (hdiag : ∀ i, 0 < L i i)
    (hfactor : P = L * L.transpose) :
    Real.log P.det = 2 * ∑ i, Real.log (L i i) := by
  have hd : L.det = ∏ i, L i i := Matrix.det_of_isLowerTriangular L htri
  have hp : 0 < L.det := by
    rw [hd]
    exact Finset.prod_pos (fun i _ => hdiag i)
  calc
    Real.log P.det = Real.log (L.det * L.det) := by
      rw [hfactor, Matrix.det_mul, Matrix.det_transpose]
    _ = Real.log L.det + Real.log L.det := Real.log_mul (ne_of_gt hp) (ne_of_gt hp)
    _ = 2 * ∑ i, Real.log (L i i) := by
      rw [hd, Real.log_prod (fun i _ => ne_of_gt (hdiag i))]
      ring

/-- Actual positive definiteness constructs a genuine positive Cholesky factor and all
three printed log-determinant quantities agree; no factor-existence conclusion is assumed. -/
theorem actual_positive_definite_matrix_has_the_full_cholesky_log_formula
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ,
      L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧ P = L * L.transpose ∧
      0 < P.det ∧
      Real.log P.det = ∑ i, Real.log (hP.isHermitian.eigenvalues i) ∧
      Real.log P.det = 2 * ∑ i, Real.log (L i i) := by
  obtain ⟨L, htri, hdiag, hfactor⟩ :=
    SafeLearning.CompleteModulesCholesky.actual_positive_definite_matrix_has_cholesky P hP
  exact ⟨L, htri, hdiag, hfactor, hP.det_pos,
    actual_positive_definite_log_determinant_is_sum_of_eigenvalue_logs P hP,
    actual_log_determinant_from_an_actual_positive_cholesky_factor P L htri hdiag hfactor⟩

/-- The adjacent displayed factor-two example is an actual matrix determinant. -/
theorem actual_displayed_two_times_identity_three_determinant :
    ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 8 := by
  rw [Matrix.det_smul, Matrix.det_one]
  norm_num

/-- The adjacent displayed regularized-kernel normalization uses the dimension exponent. -/
theorem actual_displayed_regularized_kernel_determinant_normalization
    {t : ℕ} (lambda : ℝ) (K : Matrix (Fin t) (Fin t) ℝ) :
    (lambda⁻¹ • (lambda • (1 : Matrix (Fin t) (Fin t) ℝ) + K)).det =
      (lambda⁻¹) ^ t * (lambda • (1 : Matrix (Fin t) (Fin t) ℝ) + K).det := by
  simpa only [Fintype.card_fin] using
    Matrix.det_smul (lambda • (1 : Matrix (Fin t) (Fin t) ℝ) + K) lambda⁻¹

end SafeLearning.CompleteFoundationsDeterminantLog30
