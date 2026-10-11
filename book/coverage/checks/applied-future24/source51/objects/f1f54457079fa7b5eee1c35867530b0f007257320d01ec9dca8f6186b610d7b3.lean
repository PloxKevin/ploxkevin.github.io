import SafeLearning.CompleteFoundationsQuadraticForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsBlockModels

open SafeLearning.CompleteFoundationsQuadraticForms (realQuadratic planeMatrix plane_actual_form real_psd_definition plane_pd_criterion)

def blockM : Matrix (Fin 3) (Fin 3) ℝ := !![2,1,0;1,3,0;0,0,4]
def firstBlock : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,3]
def lastBlock : Matrix (Fin 1) (Fin 1) ℝ := !![4]

theorem actual_independent_block_action (z : Fin 3 → ℝ) :
    blockM *ᵥ z=![2*z 0+z 1,z 0+3*z 1,4*z 2] := by
  ext i
  fin_cases i <;> simp [blockM,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_block_source_values :
    blockM *ᵥ (![1,2,3] : Fin 3 → ℝ)=![4,7,12] ∧
    Matrix.trace blockM=9 ∧ blockM.det=20 := by
  constructor
  · norm_num [actual_independent_block_action]
  constructor
  · norm_num [Matrix.trace,blockM,Fin.sum_univ_succ]
  · norm_num [blockM,Matrix.det_fin_three]

theorem actual_block_representation :
    blockM.submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) finSumFinEquiv=
      Matrix.fromBlocks firstBlock 0 0 lastBlock := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> norm_num [blockM,firstBlock,lastBlock,finSumFinEquiv]

theorem actual_determinant_from_blocks :
    firstBlock.det=5 ∧ lastBlock.det=4 ∧ blockM.det=firstBlock.det*lastBlock.det := by
  refine ⟨by norm_num [firstBlock,Matrix.det_fin_two],by norm_num [lastBlock,Matrix.det_unique],?_⟩
  have h := Matrix.det_submatrix_equiv_self
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) blockM
  rw [actual_block_representation,Matrix.det_fromBlocks_zero₂₁] at h
  exact h.symm

theorem generic_block_diagonal_determinant {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (Matrix.fromBlocks A 0 0 D).det=A.det*D.det :=
  Matrix.det_fromBlocks_zero₂₁ A 0 D

theorem generic_block_diagonal_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 D)=Matrix.trace A+Matrix.trace D := by
  simp [Matrix.trace,Fintype.sum_sum_type]

def schurMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := planeMatrix a 2 3

theorem actual_schur_completed_square (a : ℝ) (z : Fin 2 → ℝ) :
    realQuadratic (schurMatrix a) z=(a-4/3)*(z 0)^2+3*(z 1+2*z 0/3)^2 := by
  rw [schurMatrix,plane_actual_form]
  ring

theorem actual_schur_symmetry (a : ℝ) : (schurMatrix a).transpose=schurMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schurMatrix,planeMatrix]

theorem actual_schur_psd_iff (a : ℝ) : (schurMatrix a).PosSemidef ↔ 4/3 ≤ a := by
  rw [real_psd_definition _ (actual_schur_symmetry a)]
  constructor
  · intro h
    have hh := h (![3,-2] : Fin 2 → ℝ)
    rw [actual_schur_completed_square] at hh
    norm_num at hh
    linarith
  · intro ha z
    rw [actual_schur_completed_square]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _))
      (mul_nonneg (by norm_num) (sq_nonneg _))

theorem actual_schur_pd_iff (a : ℝ) : (schurMatrix a).PosDef ↔ 4/3 < a := by
  rw [schurMatrix,plane_pd_criterion]
  constructor
  · intro h
    nlinarith [h.2]
  · intro h
    constructor <;> nlinarith

theorem actual_schur_boundary :
    (schurMatrix (4/3)).PosSemidef ∧
    schurMatrix (4/3) *ᵥ (![3,-2] : Fin 2 → ℝ)=0 ∧
    (![3,-2] : Fin 2 → ℝ)≠0 ∧ (schurMatrix (4/3)).det=0 := by
  refine ⟨(actual_schur_psd_iff _).mpr le_rfl,?_,?_,?_⟩
  · ext i
    fin_cases i <;> norm_num [schurMatrix,planeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · norm_num [schurMatrix,planeMatrix,Matrix.det_fin_two]

theorem actual_schur_negative_direction (a : ℝ) (ha : a < 4/3) :
    realQuadratic (schurMatrix a) (![3,-2] : Fin 2 → ℝ) < 0 := by
  rw [actual_schur_completed_square]
  norm_num
  linarith

def updateV : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,1]
def updateU : Fin 2 → ℝ := ![1,2]
def updateVec : Fin 2 → ℝ := ![1/2,2]
def updatedMatrix : Matrix (Fin 2) (Fin 2) ℝ := updateV+Matrix.vecMulVec updateU updateU
def inverseCandidate : Matrix (Fin 2) (Fin 2) ℝ := (1/11 : ℝ) • !![5,-2;-2,3]

theorem actual_update_base_inverse : updateV⁻¹=Matrix.diagonal ![1/2,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [updateV,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_shared_update_quantities : updateV.det=2 ∧ updateV⁻¹ *ᵥ updateU=updateVec ∧
    updateU ⬝ᵥ updateVec=9/2 := by
  rw [actual_update_base_inverse]
  refine ⟨by norm_num [updateV,Matrix.det_fin_two,Matrix.diagonal],?_,?_⟩
  · ext i
    fin_cases i <;> norm_num [updateU,updateVec,Matrix.mulVec_diagonal]
  · norm_num [updateU,updateVec,dotProduct,Fin.sum_univ_succ]

theorem actual_rank_one_update_matrix : updatedMatrix=!![3,2;2,5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [updatedMatrix,updateV,updateU,Matrix.vecMulVec,Matrix.diagonal]

theorem actual_update_determinant : updatedMatrix.det=updateV.det*(1+updateU ⬝ᵥ updateVec) ∧
    updatedMatrix.det=11 := by
  rw [actual_rank_one_update_matrix,actual_shared_update_quantities.1,actual_shared_update_quantities.2.2]
  norm_num [Matrix.det_fin_two]

theorem actual_rank_one_inverse_formula :
    inverseCandidate=updateV⁻¹-(1/(1+updateU ⬝ᵥ updateVec) : ℝ) • Matrix.vecMulVec updateVec updateVec := by
  rw [actual_update_base_inverse,actual_shared_update_quantities.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseCandidate,updateVec,Matrix.vecMulVec,Matrix.diagonal]

theorem actual_independent_inverse_check :
    updatedMatrix*inverseCandidate=1 ∧ inverseCandidate*updatedMatrix=1 ∧
    updatedMatrix⁻¹=inverseCandidate := by
  have hr : updatedMatrix*inverseCandidate=1 := by
    rw [actual_rank_one_update_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inverseCandidate,Matrix.mul_apply,Fin.sum_univ_succ]
  have hl : inverseCandidate*updatedMatrix=1 := by
    rw [actual_rank_one_update_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inverseCandidate,Matrix.mul_apply,Fin.sum_univ_succ]
  exact ⟨hr,hl,Matrix.inv_eq_left_inv hl⟩

theorem actual_log_determinant_increase :
    Real.log updatedMatrix.det-Real.log updateV.det=Real.log (11/2) := by
  rw [actual_update_determinant.2,actual_shared_update_quantities.1]
  exact (Real.log_div (by norm_num : (11 : ℝ)≠0) (by norm_num : (2 : ℝ)≠0)).symm

theorem actual_log_determinant_decimal :
    |(Real.log updatedMatrix.det-Real.log updateV.det)-1.70475| < 0.000005 := by
  rw [actual_log_determinant_increase]
  have hb := Real.sum_range_sub_log_div_le
    (by norm_num : |(3/19 : ℝ)| < 1) 5
  norm_num [Finset.sum_range_succ] at hb
  have hlo := (abs_le.mp hb).1
  have hhi := (abs_le.mp hb).2
  have hlog : Real.log (11/2)=Real.log (11/8)+2*Real.log 2 := by
    have hm := Real.log_mul (by norm_num : (11/8 : ℝ)≠0) (by norm_num : (4 : ℝ)≠0)
    have hp := Real.log_pow (2 : ℝ) 2
    norm_num at hm hp
    rw [hm,hp]
  rw [hlog,abs_lt]
  constructor <;> nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

end SafeLearning.CompleteFoundationsBlockModels
