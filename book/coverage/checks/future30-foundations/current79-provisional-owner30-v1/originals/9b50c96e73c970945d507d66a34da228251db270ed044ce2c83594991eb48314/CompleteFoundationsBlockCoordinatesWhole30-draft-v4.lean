import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Matrix BigOperators MatrixOrder
namespace SafeLearning.CompleteFoundationsBlockCoordinates30

theorem actual_compatible_block_action {n m p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix n p ℝ) (B : Matrix n q ℝ) (C : Matrix m p ℝ) (D : Matrix m q ℝ)
    (x : p → ℝ) (u : q → ℝ) :
    Matrix.fromBlocks A B C D *ᵥ Sum.elim x u =
      Sum.elim (A *ᵥ x + B *ᵥ u) (C *ᵥ x + D *ᵥ u) := by
  rw [Matrix.fromBlocks_mulVec]
  rfl

theorem actual_symmetric_block_quadratic_cross_term {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m m ℝ)
    (x : n → ℝ) (y : m → ℝ) :
    Sum.elim x y ⬝ᵥ (Matrix.fromBlocks A B Bᵀ C *ᵥ Sum.elim x y) =
      x ⬝ᵥ (A *ᵥ x) + 2 * (x ⬝ᵥ (B *ᵥ y)) + y ⬝ᵥ (C *ᵥ y) := by
  rw [actual_compatible_block_action, sumElim_dotProduct_sumElim,
    dotProduct_add, dotProduct_add]
  have hcross : y ⬝ᵥ (Bᵀ *ᵥ x) = x ⬝ᵥ (B *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hcross]
  ring

variable {Block : Type*} [Fintype Block] [DecidableEq Block]
    {Size : Block → Type*} [∀ b, Fintype (Size b)] [∀ b, DecidableEq (Size b)]

private theorem copied_actual_psd_iff_true_Gram {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) : M.PosSemidef ↔ ∃ F : Matrix I I ℝ, M = Fᵀ * F := by
  constructor
  · intro hM
    obtain ⟨F,hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
    exact ⟨F,by simpa [Matrix.star_eq_conjTranspose] using hF⟩
  · rintro ⟨F,rfl⟩
    simpa using Matrix.posSemidef_conjTranspose_mul_self F

theorem actual_all_block_LMIs_iff_actual_block_diagonal_LMI
    (M : ∀ b, Matrix (Size b) (Size b) ℝ) :
    (Matrix.blockDiagonal' M).PosSemidef ↔ ∀ b, (M b).PosSemidef := by
  constructor
  · intro h b
    have hs := h.submatrix (fun i : Size b => (⟨b,i⟩ : Sigma Size))
    have he : (Matrix.blockDiagonal' M).submatrix
        (fun i : Size b => (⟨b,i⟩ : Sigma Size))
        (fun i : Size b => (⟨b,i⟩ : Sigma Size)) = M b := by
      ext i j
      simp [Matrix.submatrix_apply,Matrix.blockDiagonal'_apply]
    rwa [he] at hs
  · intro h
    choose F hF using fun b => (copied_actual_psd_iff_true_Gram (M b)).mp (h b)
    have he : Matrix.blockDiagonal' M = (Matrix.blockDiagonal' F)ᵀ * Matrix.blockDiagonal' F := by
      rw [Matrix.blockDiagonal'_transpose,←Matrix.blockDiagonal'_mul]
      congr 1
      funext b
      exact hF b
    rw [he]
    simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockDiagonal' F)

def actualSelection (b : Block) : Matrix (Size b) (Sigma Size) ℝ :=
  fun i j => if j = ⟨b,i⟩ then 1 else 0

theorem actual_selection_extracts_each_stack_component (b : Block) (z : Sigma Size → ℝ) :
    actualSelection b *ᵥ z = fun i => z ⟨b,i⟩ := by
  ext i
  simp [actualSelection, Matrix.mulVec, dotProduct]

theorem actual_selection_transpose_puts_back_the_component (b : Block) (x : Size b → ℝ)
    (i : Size b) : ((actualSelection b)ᵀ *ᵥ x) ⟨b,i⟩ = x i := by
  simp [actualSelection, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem actual_selection_transpose_zero_pads_every_other_block
    (b c : Block) (hc : c ≠ b) (x : Size b → ℝ) (j : Size c) :
    ((actualSelection b)ᵀ *ᵥ x) ⟨c,j⟩ = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, actualSelection]
  apply Finset.sum_eq_zero
  intro i _
  have hne : (⟨c,j⟩ : Sigma Size) ≠ ⟨b,i⟩ := by
    intro he
    exact hc (congrArg Sigma.fst he)
  simp [hne]

end SafeLearning.CompleteFoundationsBlockCoordinates30
