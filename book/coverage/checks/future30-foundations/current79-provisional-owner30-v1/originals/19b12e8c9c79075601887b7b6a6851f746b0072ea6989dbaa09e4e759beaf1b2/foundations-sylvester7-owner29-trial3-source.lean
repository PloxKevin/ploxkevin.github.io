import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Matrix BigOperators
namespace SafeLearning.CompleteFoundationsSylvester30

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem actual_rectangular_sylvester_determinant_identity
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    (1 + A*B).det = (1 + B*A).det :=
  Matrix.det_one_add_mul_comm A B

theorem actual_rectangular_complex_characteristic_polynomial_identity
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    (Polynomial.X : Polynomial ℂ)^(Fintype.card n)*(A*B).charpoly =
      Polynomial.X^(Fintype.card m)*(B*A).charpoly :=
  Matrix.charpoly_mul_comm' A B

theorem actual_rectangular_products_have_identical_nonzero_eigenvalue_multiplicities
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (z : ℂ) (hz : z ≠ 0) :
    (A*B).charpoly.roots.count z = (B*A).charpoly.roots.count z := by
  classical
  have h := congrArg (fun p : Polynomial ℂ => p.roots.count z)
    (actual_rectangular_complex_characteristic_polynomial_identity A B)
  rw [Polynomial.roots_mul (mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero) (A*B).charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero) (B*A).charpoly_monic.ne_zero)] at h
  simpa [Polynomial.roots_X_pow, Multiset.count_add, hz] using h

theorem actual_rectangular_products_have_identical_full_nonzero_eigenvalue_multisets
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    (A*B).charpoly.roots.filter (fun z => z ≠ 0) =
      (B*A).charpoly.roots.filter (fun z => z ≠ 0) := by
  classical
  apply Multiset.ext.mpr
  intro z
  by_cases hz : z=0
  · simp [hz]
  · simpa only [Multiset.count_filter, if_pos hz] using
      actual_rectangular_products_have_identical_nonzero_eigenvalue_multiplicities A B z hz

theorem actual_rectangular_products_have_the_same_nonzero_complex_spectrum
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ (A*B) ↔ z ∈ spectrum ℂ (B*A) := by
  classical
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    ← Polynomial.mem_roots (A*B).charpoly_monic.ne_zero,
    ← Polynomial.mem_roots (B*A).charpoly_monic.ne_zero,
    ← Multiset.count_pos, ← Multiset.count_pos,
    actual_rectangular_products_have_identical_nonzero_eigenvalue_multiplicities A B z hz]

theorem actual_real_rectangular_products_have_identical_complexified_nonzero_eigenvalue_multisets
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    ((A*B).map (algebraMap ℝ ℂ)).charpoly.roots.filter (fun z => z ≠ 0) =
      ((B*A).map (algebraMap ℝ ℂ)).charpoly.roots.filter (fun z => z ≠ 0) := by
  classical
  simpa only [← Matrix.map_mul] using
    actual_rectangular_products_have_identical_full_nonzero_eigenvalue_multisets
      (A.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ))

-- The inverse expression has its ordinary nonsingular domain, as in the preceding block section.
-- This elementary determinant-lemma proof is reused from the fully read selected UniversalMatrices.
theorem actual_full_matrix_determinant_lemma
    (V : Matrix n n ℝ) (hV : IsUnit V.det) (u v : n → ℝ) :
    (V+Matrix.vecMulVec u v).det=V.det*(1+v ⬝ᵥ (V⁻¹ *ᵥ u)) := by
  have h := Matrix.det_add_mul (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) v) hV
  have ho : Matrix.replicateCol (Fin 1) u*Matrix.replicateRow (Fin 1) v=Matrix.vecMulVec u v := by
    ext i j
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.vecMulVec]
  rw [ho,Matrix.det_fin_one] at h
  simp [Matrix.mul_apply,Matrix.replicateRow,Matrix.replicateCol,Fin.sum_univ_succ,Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simpa [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc] using h

end SafeLearning.CompleteFoundationsSylvester30
