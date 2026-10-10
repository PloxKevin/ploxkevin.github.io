import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsRankOneSchur

def sourceC : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,4]
def sourcePlus : Matrix (Fin 2) (Fin 2) ℝ := !![1/25,2/25;2/25,4/25]
def sourceB : Fin 2 → ℝ := ![1,0]
def direction : Fin 2 → ℝ := ![1,2]
def nullVector : Fin 2 → ℝ := ![2,-1]
def unitDirection : Fin 2 → ℝ := ![1/Real.sqrt 5,2/Real.sqrt 5]
def orthogonalFrame : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/Real.sqrt 5,-2/Real.sqrt 5;2/Real.sqrt 5,1/Real.sqrt 5]
def singularDiagonal : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![5,0]
def rangeProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1/5,2/5;2/5,4/5]

def moorePenrose (A B : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  A*B*A=A ∧ B*A*B=B ∧ (A*B)ᵀ=A*B ∧ (B*A)ᵀ=B*A

theorem actual_moore_penrose_identities : moorePenrose sourceC sourcePlus := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceC,sourcePlus,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_range_projection : sourceC*sourcePlus=rangeProjection ∧
    sourcePlus*sourceC=rangeProjection := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sourceC,sourcePlus,rangeProjection,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_moore_penrose_unique (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : moorePenrose sourceC B) : B=sourcePlus := by
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hB.1
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hB.2.2.1
  have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hB.2.2.2
  simp [sourceC,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
  have hCB : sourceC*B=rangeProjection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceC,rangeProjection,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith
  have hBC : B*sourceC=rangeProjection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceC,rangeProjection,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith
  have hMP := hB.2.1
  rw [hBC] at hMP
  ext i j
  have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hMP
  have hj := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hCB
  fin_cases i <;> fin_cases j <;>
    simp [sourceC,sourcePlus,rangeProjection,Matrix.mul_apply,Fin.sum_univ_succ] at hi hj ⊢ <;>
      nlinarith

theorem actual_pseudoinverse_scalar_formula : sourcePlus=(1/25 : ℝ) • sourceC := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourcePlus,sourceC]

theorem actual_unit_direction : unitDirection ⬝ᵥ unitDirection=1 := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  simp [unitDirection,dotProduct,Fin.sum_univ_succ]
  field_simp
  nlinarith

theorem actual_rank_one_factorization :
    sourceC=5 • Matrix.vecMulVec unitDirection unitDirection ∧
    sourcePlus=(1/5 : ℝ) • Matrix.vecMulVec unitDirection unitDirection := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sourceC,sourcePlus,unitDirection,Matrix.vecMulVec] <;>
      field_simp <;> nlinarith

theorem actual_orthogonal_frame : orthogonalFrameᵀ*orthogonalFrame=1 ∧
    orthogonalFrame*orthogonalFrameᵀ=1 := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [orthogonalFrame,Matrix.mul_apply,Fin.sum_univ_succ] <;>
      field_simp <;> nlinarith

theorem actual_singular_value_decomposition :
    orthogonalFrame*singularDiagonal*orthogonalFrameᵀ=sourceC := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthogonalFrame,singularDiagonal,sourceC,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] <;>
      field_simp <;> nlinarith

theorem actual_rank : sourceC.rank=1 := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := !![1,-2;2,1]
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
  have hS : S.det≠0 := by norm_num [S,Matrix.det_fin_two]
  have hST : Sᵀ.det≠0 := by simpa using hS
  have hC : sourceC=S*D*Sᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceC,S,D,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
  rw [hC,Matrix.rank_mul_eq_left_of_det_ne_zero Sᵀ (S*D) hST,
    Matrix.rank_mul_eq_right_of_det_ne_zero S D hS]
  simp only [D,Matrix.rank_diagonal,Fintype.card_subtype]
  have he : ({i : Fin 2 | ![(1 : ℝ),0] i≠0} : Finset (Fin 2))={0} := by
    ext i
    fin_cases i <;> simp
  rw [he]
  simp

theorem actual_all_range_vectors (y : Fin 2 → ℝ) :
    y∈Set.range (fun x : Fin 2 → ℝ => sourceC *ᵥ x) ↔
      ∃ s : ℝ,y=s • direction := by
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨x 0+2*x 1,?_⟩
    ext i
    fin_cases i <;> simp [sourceC,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

  · rintro ⟨s,rfl⟩
    refine ⟨![s,0],?_⟩
    ext i
    fin_cases i <;> simp [sourceC,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem actual_source_psd : sourceC.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sourceC]
  · intro x
    have he : star x ⬝ᵥ (sourceC *ᵥ x)=(x 0+2*x 1)^2 := by
      simp [sourceC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    rw [he]
    exact sq_nonneg _

theorem actual_gram_matrix : sourceCᵀ*sourceC=5 • sourceC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceC,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_all_eigenvalues (ev : ℝ) (x : Fin 2 → ℝ) (hx : x≠0)
    (he : sourceC *ᵥ x=ev • x) : ev=0 ∨ ev=5 := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp [sourceC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1
  by_cases hev : ev=0
  · exact Or.inl hev
  · have hr : ev*(x 1-2*x 0)=0 := by nlinarith
    have hrel := (mul_eq_zero.mp hr).resolve_left hev
    have hx0 : x 0≠0 := by
      intro hz
      apply hx
      ext i
      fin_cases i <;> simp <;> nlinarith
    have hv : (5-ev)*x 0=0 := by nlinarith
    have hh := (mul_eq_zero.mp hv).resolve_right hx0
    exact Or.inr (by linarith)

def isSingularValue (σ : ℝ) : Prop :=
  0≤σ ∧ ∃ x : Fin 2 → ℝ,x≠0 ∧ (sourceCᵀ*sourceC) *ᵥ x=σ^2 • x

theorem actual_exact_singular_values (σ : ℝ) : isSingularValue σ ↔ σ=5 ∨ σ=0 := by
  constructor
  · rintro ⟨hσ,x,hx,he⟩
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    rw [actual_gram_matrix] at h0 h1
    simp [sourceC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1
    have hC : sourceC *ᵥ x=(σ^2/5) • x := by
      ext i
      fin_cases i <;> simp [sourceC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
        nlinarith [h0,h1]
    rcases actual_all_eigenvalues (σ^2/5) x hx hC with hz | hf
    · exact Or.inr (by nlinarith)
    · exact Or.inl (by nlinarith)
  · rintro (rfl | rfl)
    · refine ⟨by norm_num,direction,?_,?_⟩
      · intro h
        have h0 := congrFun h 0
        norm_num [direction] at h0
      · rw [actual_gram_matrix]
        ext i
        fin_cases i <;> norm_num [sourceC,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    · refine ⟨by norm_num,nullVector,?_,?_⟩
      · intro h
        have h0 := congrFun h 0
        norm_num [nullVector] at h0
      · rw [actual_gram_matrix]
        ext i
        fin_cases i <;> norm_num [sourceC,nullVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_pseudoinverse_solution_and_residual :
    sourcePlus *ᵥ sourceB=![1/25,2/25] ∧
    sourceC *ᵥ (sourcePlus *ᵥ sourceB)=![1/5,2/5] ∧
    sourceB-sourceC *ᵥ (sourcePlus *ᵥ sourceB)=![4/5,-2/5] ∧
    (1-sourceC*sourcePlus) *ᵥ sourceB=![4/5,-2/5] := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    ext i
    fin_cases i <;>
      norm_num [sourcePlus,sourceB,sourceC,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_succ]

theorem actual_residual_orthogonal_to_whole_range (y : Fin 2 → ℝ)
    (hy : y∈Set.range (fun x : Fin 2 → ℝ => sourceC *ᵥ x)) :
    (sourceB-sourceC *ᵥ (sourcePlus *ᵥ sourceB)) ⬝ᵥ y=0 := by
  obtain ⟨s,rfl⟩ := (actual_all_range_vectors y).mp hy
  rw [actual_pseudoinverse_solution_and_residual.2.2.1]
  simp [direction,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_source_not_in_range :
    sourceB∉Set.range (fun x : Fin 2 → ℝ => sourceC *ᵥ x) := by
  intro h
  obtain ⟨s,hs⟩ := (actual_all_range_vectors sourceB).mp h
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  simp [sourceB,direction] at h0 h1
  linarith

theorem actual_range_condition_fails : (1-sourceC*sourcePlus) *ᵥ sourceB≠0 := by
  rw [actual_pseudoinverse_solution_and_residual.2.2.2]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

def sourceBlock (a : ℝ) (β : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a,β 0,β 1;β 0,1,2;β 1,2,4]

theorem actual_block_hermitian (a : ℝ) (β : Fin 2 → ℝ) :
    (sourceBlock a β).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceBlock]

theorem actual_block_quadratic (a : ℝ) (β : Fin 2 → ℝ) (z : Fin 3 → ℝ) :
    z ⬝ᵥ (sourceBlock a β *ᵥ z)=
      a*z 0^2+2*z 0*(β 0*z 1+β 1*z 2)+(z 1+2*z 2)^2 := by
  simp [sourceBlock,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_block_completed_square (a s : ℝ) (z : Fin 3 → ℝ) :
    z ⬝ᵥ (sourceBlock a (s • direction) *ᵥ z)=
      (a-s^2)*z 0^2+(s*z 0+z 1+2*z 2)^2 := by
  rw [actual_block_quadratic]
  simp [direction]
  ring

theorem actual_singular_schur_iff (a : ℝ) (β : Fin 2 → ℝ) :
    (sourceBlock a β).PosSemidef ↔ ∃ s : ℝ,β=s • direction ∧ s^2≤a := by
  constructor
  · intro hM
    have hform (z : Fin 3 → ℝ) : 0≤z ⬝ᵥ (sourceBlock a β *ᵥ z) := by
      simpa using hM.dotProduct_mulVec_nonneg z
    have hd : 2*β 0-β 1=0 := by
      by_contra hn
      let t : ℝ := -(a+1)/(2*(2*β 0-β 1))
      have hh := hform ![1,2*t,-t]
      rw [actual_block_quadratic] at hh
      norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.isValue] at hh
      have he : a+2*(β 0*(2*t)+β 1*(-t)) = -1 := by
        dsimp [t]
        field_simp
        ring
      nlinarith [he]
    have hb : β=β 0 • direction := by
      ext i
      fin_cases i <;> simp [direction] <;> linarith
    refine ⟨β 0,hb,?_⟩
    have hh := hform ![1,-β 0,0]
    rw [hb,actual_block_completed_square] at hh
    simp [direction] at hh
    linarith
  · rintro ⟨s,rfl,hs⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (actual_block_hermitian a (s • direction))
    intro z
    simp only [star_trivial]
    rw [actual_block_completed_square]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg _)) (sq_nonneg _)

theorem actual_range_schur_term (s : ℝ) :
    sourcePlus *ᵥ (s • direction)=![s/5,2*s/5] ∧
      (s • direction) ⬝ᵥ (sourcePlus *ᵥ (s • direction))=s^2 := by
  constructor
  · ext i
    fin_cases i <;> simp [sourcePlus,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  · simp [sourcePlus,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring

theorem actual_null_vector : sourceC *ᵥ nullVector=0 ∧ nullVector≠0 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [sourceC,nullVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · intro h
    have h0 := congrFun h 0
    norm_num [nullVector] at h0

theorem actual_incompatible_quadratic (a x t : ℝ) :
    ![x,2*t,-t] ⬝ᵥ (sourceBlock a sourceB *ᵥ ![x,2*t,-t])=a*x^2+4*t*x := by
  rw [actual_block_quadratic]
  simp [sourceB]
  ring

theorem actual_no_top_corner_repairs_range (a : ℝ) :
    ¬(sourceBlock a sourceB).PosSemidef ∧
      ![1,2*(-(a+1)/4),-(-(a+1)/4)] ⬝ᵥ
        (sourceBlock a sourceB *ᵥ ![1,2*(-(a+1)/4),-(-(a+1)/4)]) = -1 := by
  have hh : ![1,2*(-(a+1)/4),-(-(a+1)/4)] ⬝ᵥ
      (sourceBlock a sourceB *ᵥ ![1,2*(-(a+1)/4),-(-(a+1)/4)]) = -1 := by
    rw [actual_incompatible_quadratic]
    ring
  refine ⟨?_,hh⟩
  intro h
  have hn := h.dotProduct_mulVec_nonneg ![1,2*(-(a+1)/4),-(-(a+1)/4)]
  have hn' : 0≤ ![1,2*(-(a+1)/4),-(-(a+1)/4)] ⬝ᵥ
      (sourceBlock a sourceB *ᵥ ![1,2*(-(a+1)/4),-(-(a+1)/4)]) := by
    simpa only [star_trivial] using hn
  rw [hh] at hn'
  linarith

end SafeLearning.CompleteFoundationsRankOneSchur
