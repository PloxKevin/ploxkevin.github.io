import SafeLearning.CompleteModulesSDPCone

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesSDPBlocks
open CompleteModulesSDPCone

variable {Block : Type*} [Fintype Block] [DecidableEq Block]
  {Size : Block→Type*} [∀ block,Fintype (Size block)] [∀ block,DecidableEq (Size block)]

theorem actual_many_psd_constraints_iff_the_true_block_diagonal_matrix_is_psd
    (matrix : ∀ block,Matrix (Size block) (Size block) ℝ) :
    (Matrix.blockDiagonal' matrix).PosSemidef ↔ ∀ block,(matrix block).PosSemidef := by
  constructor
  · intro h block
    have hs := h.submatrix (fun index : Size block => (⟨block,index⟩ : Sigma Size))
    have he : (Matrix.blockDiagonal' matrix).submatrix
        (fun index : Size block => (⟨block,index⟩ : Sigma Size))
        (fun index : Size block => (⟨block,index⟩ : Sigma Size))=matrix block := by
      ext row column
      simp [Matrix.submatrix_apply,Matrix.blockDiagonal'_apply]
    rwa [he] at hs
  · intro h
    choose factor hfactor using fun block =>
      (actual_psd_iff_true_transpose_gram_factorization (matrix block)).mp (h block)
    have he : Matrix.blockDiagonal' matrix=
        (Matrix.blockDiagonal' factor)ᵀ*Matrix.blockDiagonal' factor := by
      rw [Matrix.blockDiagonal'_transpose,←Matrix.blockDiagonal'_mul]
      congr 1
      funext block
      exact hfactor block
    rw [he]
    simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockDiagonal' factor)

theorem actual_scalar_linear_inequality_is_a_one_by_one_lmi (objective bound : ℝ) :
    (!![bound-objective] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef ↔ objective≤bound := by
  have he : (!![bound-objective] : Matrix (Fin 1) (Fin 1) ℝ)=Matrix.diagonal (fun _ => bound-objective) := by
    ext row column;fin_cases row;fin_cases column;simp
  rw [he,Matrix.posSemidef_diagonal_iff]
  simp

theorem actual_strict_scalar_linear_inequality_is_a_one_by_one_strict_lmi (objective bound : ℝ) :
    (!![bound-objective] : Matrix (Fin 1) (Fin 1) ℝ).PosDef ↔ objective<bound := by
  have he : (!![bound-objective] : Matrix (Fin 1) (Fin 1) ℝ)=Matrix.diagonal (fun _ => bound-objective) := by
    ext row column;fin_cases row;fin_cases column;simp
  rw [he,Matrix.posDef_diagonal_iff]
  simp

variable {Constraint Parameter : Type*} [Fintype Constraint] [DecidableEq Constraint]
  [Fintype Parameter]

def actualLinearProgramDiagonalMatrix (system : Matrix Constraint Parameter ℝ)
    (budget : Constraint→ℝ) (unknown : Parameter→ℝ) : Matrix Constraint Constraint ℝ :=
  Matrix.diagonal (budget-system*ᵥ unknown)

omit [Fintype Constraint] in
theorem actual_all_linear_program_inequalities_iff_the_true_diagonal_lmi
    (system : Matrix Constraint Parameter ℝ) (budget : Constraint→ℝ) (unknown : Parameter→ℝ) :
    (actualLinearProgramDiagonalMatrix system budget unknown).PosSemidef ↔
      ∀ constraint,(system*ᵥ unknown) constraint≤budget constraint := by
  simp [actualLinearProgramDiagonalMatrix,Matrix.posSemidef_diagonal_iff,Pi.sub_apply]

omit [Fintype Constraint] in
theorem actual_linear_program_diagonal_matrix_is_the_literal_affine_lmi
    (system : Matrix Constraint Parameter ℝ) (budget : Constraint→ℝ) (unknown : Parameter→ℝ) :
    actualLinearProgramDiagonalMatrix system budget unknown=
      Matrix.diagonal budget+∑ parameter,unknown parameter •
        Matrix.diagonal (fun constraint => -(system constraint parameter)) := by
  ext row column
  by_cases he : row=column
  · subst column
    simp [actualLinearProgramDiagonalMatrix,Matrix.sum_apply,
      Matrix.smul_apply,Matrix.mulVec,dotProduct,Pi.sub_apply,Finset.sum_neg_distrib]
    have hs : (∑ parameter,system row parameter*unknown parameter)=
        ∑ parameter,unknown parameter*system row parameter := by
      apply Finset.sum_congr rfl
      intro parameter _
      ring
    rw [hs];ring
  · simp [actualLinearProgramDiagonalMatrix,Matrix.sum_apply,Matrix.smul_apply,he]

end SafeLearning.CompleteModulesSDPBlocks
