import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Matrix BigOperators
namespace SafeLearning.CompleteFoundationsWoodburyPushThrough30
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem actual_full_rectangular_Woodbury (A : Matrix n n ℝ) (U : Matrix n m ℝ)
    (C : Matrix m m ℝ) (V : Matrix m n ℝ) (hA : IsUnit A) (hC : IsUnit C)
    (hS : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub A U C V hA hC hS

theorem actual_rank_one_double_product (A : Matrix n n ℝ) (u v : n → ℝ) :
    Matrix.vecMulVec u v * A * Matrix.vecMulVec u v =
      (v ⬝ᵥ (A *ᵥ u)) • Matrix.vecMulVec u v := by
  rw [Matrix.mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul]

theorem actual_full_rank_one_inverse (A : Matrix n n ℝ) (u v : n → ℝ)
    (hA : IsUnit A) (hq : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + Matrix.vecMulVec u v)⁻¹ = A⁻¹ -
      (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • (A⁻¹ * Matrix.vecMulVec u v * A⁻¹) := by
  apply Matrix.inv_eq_right_inv
  have hAA := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hE := actual_rank_one_double_product A⁻¹ u v
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  rw [hE, Matrix.smul_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  <;> ring

theorem actual_rectangular_intertwining (Phi : Matrix m n ℝ) (lambda : ℝ) :
    Phiᵀ * (lambda • (1 : Matrix m m ℝ) + Phi * Phiᵀ) =
    (lambda • (1 : Matrix n n ℝ) + Phiᵀ * Phi) * Phiᵀ := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem actual_positive_regularization_both_Gram_inverses (Phi : Matrix m n ℝ)
    (lambda : ℝ) (hl : 0 < lambda) :
    (lambda • (1 : Matrix n n ℝ) + Phiᵀ * Phi).PosDef ∧
    (lambda • (1 : Matrix m m ℝ) + Phi * Phiᵀ).PosDef := by
  have hN : (lambda • (1 : Matrix n n ℝ)).PosDef := Matrix.PosDef.one.smul hl
  have hM : (lambda • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hl
  have hG : (Phiᵀ * Phi).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Phi
  have hK : (Phi * Phiᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Phi
  exact ⟨hN.add_posSemidef hG, hM.add_posSemidef hK⟩

theorem actual_positive_regularization_push_through (Phi : Matrix m n ℝ)
    (lambda : ℝ) (hl : 0 < lambda) :
    (lambda • (1 : Matrix n n ℝ) + Phiᵀ * Phi)⁻¹ * Phiᵀ =
      Phiᵀ * (lambda • (1 : Matrix m m ℝ) + Phi * Phiᵀ)⁻¹ := by
  let A := lambda • (1 : Matrix n n ℝ) + Phiᵀ * Phi
  let B := lambda • (1 : Matrix m m ℝ) + Phi * Phiᵀ
  have h := actual_positive_regularization_both_Gram_inverses Phi lambda hl
  have hA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.1.isUnit
  have hB : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp h.2.isUnit
  have he : Phiᵀ * B = A * Phiᵀ := actual_rectangular_intertwining Phi lambda
  calc
    A⁻¹ * Phiᵀ = A⁻¹ * Phiᵀ * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hB, Matrix.mul_one]
    _ = A⁻¹ * (Phiᵀ * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * (A * Phiᵀ) * B⁻¹ := by rw [he]
    _ = Phiᵀ * B⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left A Phiᵀ hA]

end SafeLearning.CompleteFoundationsWoodburyPushThrough30
