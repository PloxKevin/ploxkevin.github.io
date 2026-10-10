import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsUniversalMatrices

theorem actual_orthogonal_matrix_preserves_norm {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Qᵀ*Q=1) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Q x‖=‖x‖ := by
  have h : (Q *ᵥ (x : n → ℝ)) ⬝ᵥ (Q *ᵥ (x : n → ℝ))=(x : n → ℝ) ⬝ᵥ (x : n → ℝ) := by
    rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,Matrix.mulVec_mulVec,hQ,Matrix.one_mulVec]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(Q *ᵥ (x : n → ℝ)) i^2)=(∑ i,(x i)^2)
  simpa only [dotProduct,pow_two] using h

theorem actual_orthogonal_matrix_is_invertible {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Qᵀ*Q=1) : IsUnit Q := by
  have hd := congrArg Matrix.det hQ
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hd
  apply (Matrix.isUnit_iff_isUnit_det Q).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz,zero_mul] at hd
  norm_num at hd

theorem actual_equal_images_iff_null_difference {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (x y : n → ℝ) : A *ᵥ x=A *ᵥ y ↔ A *ᵥ (x-y)=0 := by
  rw [Matrix.mulVec_sub,sub_eq_zero]

theorem actual_matrix_determinant_lemma {n : Type*} [Fintype n] [DecidableEq n]
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

theorem actual_sylvester_determinant_identity {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    (1+A*B).det=(1+B*A).det := Matrix.det_one_add_mul_comm A B

end SafeLearning.CompleteFoundationsUniversalMatrices
