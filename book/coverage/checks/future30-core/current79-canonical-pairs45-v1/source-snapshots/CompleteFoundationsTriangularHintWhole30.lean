import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsTriangularHint30

theorem actual_upper_triangular_characteristic_polynomial
    {n R : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [CommRing R]
    (A : Matrix n n R) (hA : A.IsUpperTriangular) :
    A.charpoly = ∏ i : n, (Polynomial.X - Polynomial.C (A i i)) :=
  Matrix.charpoly_of_isUpperTriangular A hA

theorem actual_upper_triangular_eigenvalue_multiset
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℂ) (hA : A.IsUpperTriangular) :
    A.charpoly.roots = Finset.univ.val.map (fun i : n => A i i) := by
  classical
  rw [actual_upper_triangular_characteristic_polynomial A hA,
    Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (A i i))

theorem actual_upper_triangular_complex_eigenvalue_iff_diagonal
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℂ) (hA : A.IsUpperTriangular) (z : ℂ) :
    z ∈ spectrum ℂ A ↔ ∃ i : n, z = A i i := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    actual_upper_triangular_characteristic_polynomial A hA,
    Polynomial.isRoot_prod]
  simp [Polynomial.IsRoot, sub_eq_zero]

theorem actual_real_upper_triangular_complex_eigenvalue_iff_diagonal
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℝ) (hA : A.IsUpperTriangular) (z : ℂ) :
    z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) ↔ ∃ i : n, z = (A i i : ℂ) := by
  have hc : (A.map (algebraMap ℝ ℂ)).IsUpperTriangular :=
    Matrix.BlockTriangular.map (algebraMap ℝ ℂ) hA
  simpa using actual_upper_triangular_complex_eigenvalue_iff_diagonal
    (A.map (algebraMap ℝ ℂ)) hc z

def actualRealQuadratic {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

def actualSymmetricPart {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + A.transpose)

private theorem actual_quadratic_transpose {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    actualRealQuadratic A.transpose x = actualRealQuadratic A x := by
  unfold actualRealQuadratic
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose, dotProduct_comm]

theorem actual_real_quadratic_uses_only_symmetric_part
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) :
    actualRealQuadratic (actualSymmetricPart A) x = actualRealQuadratic A x := by
  unfold actualSymmetricPart actualRealQuadratic
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add]
  change (1 / 2 : ℝ) *
    (actualRealQuadratic A x + actualRealQuadratic A.transpose x) = actualRealQuadratic A x
  rw [actual_quadratic_transpose]
  ring

theorem actual_symmetric_part_is_symmetric
    {n : Type*} (A : Matrix n n ℝ) :
    (actualSymmetricPart A).transpose = actualSymmetricPart A := by
  simp [actualSymmetricPart, Matrix.transpose_add, add_comm]

end SafeLearning.CompleteFoundationsTriangularHint30
