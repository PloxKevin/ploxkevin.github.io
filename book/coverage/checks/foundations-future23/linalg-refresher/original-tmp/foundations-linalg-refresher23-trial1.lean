import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsLinalgRefresher23

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;0,1]
def B : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;1,3]
def Ainverse : Matrix (Fin 2) (Fin 2) ℝ := !![1,-2;0,1]
def R : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,4]
def M : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,2]

theorem actual_rectangular_output_is_the_row_dot_product
    {m n : Type*} [Fintype n] (C : Matrix m n ℝ) (x : n → ℝ) (i : m) :
    (C *ᵥ x) i = ∑ j, C i j*x j := rfl

theorem actual_rectangular_product_applies_right_matrix_first
    {m n p : Type*} [Fintype n] [Fintype p]
    (C : Matrix m n ℝ) (D : Matrix n p ℝ) (x : p → ℝ) :
    (C*D)*ᵥx=C*ᵥ(D*ᵥx) := (Matrix.mulVec_mulVec x C D).symm

theorem actual_product_column_is_left_matrix_times_right_column
    {m n p : Type*} [Fintype n]
    (C : Matrix m n ℝ) (D : Matrix n p ℝ) (j : p) :
    (fun i => (C*D) i j)=C*ᵥ(fun k=>D k j) := rfl

theorem actual_printed_A_action (x : Fin 2 → ℝ) :
    A*ᵥx=![x 0+2*x 1,x 1] := by
  ext i;fin_cases i <;> simp [A,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_printed_A_times_one_two : A*ᵥ![1,2]=![5,2] := by
  rw [actual_printed_A_action];norm_num

theorem actual_printed_two_matrix_products :
    A*B=!![4,6;1,3] ∧ B*A=!![2,4;1,5] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [A,B,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_printed_products_cannot_be_reordered : A*B≠B*A := by
  intro h
  have hc := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℝ => C 0 0) h
  norm_num [A,B,Matrix.mul_apply,Fin.sum_univ_two] at hc

theorem actual_transpose_swaps_entries
    {m n : Type*} (C : Matrix m n ℝ) (i : n) (j : m) : Cᵀ i j=C j i := rfl

theorem actual_rectangular_transpose_reverses_product
    {m n p : Type*} [Fintype n] (C : Matrix m n ℝ) (D : Matrix n p ℝ) :
    (C*D)ᵀ=Dᵀ*Cᵀ := Matrix.transpose_mul C D

theorem actual_printed_transpose_and_square : Aᵀ=!![1,0;2,1] ∧ A^2=A*A := by
  constructor
  · ext i j;fin_cases i <;> fin_cases j <;> norm_num [A,Matrix.transpose]
  · exact pow_two A

theorem actual_printed_backward_substitution (x : Fin 2 → ℝ) :
    A*ᵥx=![5,2] ↔ x=![1,2] := by
  constructor
  · intro h
    rw [actual_printed_A_action] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
    ext i;fin_cases i <;> simp <;> linarith
  · intro h;rw [h];exact actual_printed_A_times_one_two

theorem actual_printed_two_sided_inverse : Ainverse*A=1 ∧ A*Ainverse=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [A,Ainverse,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_real_square_inverse_iff_determinant_nonzero
    {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ) :
    C.det≠0 ↔ ∃ D : Matrix n n ℝ, D*C=1 ∧ C*D=1 := by
  constructor
  · intro hc
    have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hc
    exact ⟨C⁻¹,C.nonsing_inv_mul hu,C.mul_nonsing_inv hu⟩
  · rintro ⟨D,_,h⟩ hz
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at hd
    norm_num at hd

theorem actual_two_by_two_and_printed_determinants (a b c d : ℝ) :
    (Matrix.det !![a,b;c,d]=a*d-b*c) ∧ A.det=1 ∧ R.det=0 := by
  refine ⟨Matrix.det_fin_two_of a b c d,?_,?_⟩ <;> norm_num [A,R,Matrix.det_fin_two]

theorem actual_printed_rank_one_action (x : Fin 2 → ℝ) :
    R*ᵥx=![x 0+2*x 1,2*(x 0+2*x 1)] := by
  ext i;fin_cases i <;> simp [R,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring

theorem actual_printed_nullspace_all_vectors (x : Fin 2 → ℝ) :
    R*ᵥx=0 ↔ ∃ t : ℝ, x=t • ![-2,1] := by
  constructor
  · intro h
    rw [actual_printed_rank_one_action] at h
    have h0 := congrFun h 0
    simp only [Fin.isValue,Matrix.cons_val_zero,Pi.zero_apply] at h0
    refine ⟨x 1,?_⟩
    ext i;fin_cases i <;> simp <;> linarith
  · rintro ⟨t,rfl⟩
    rw [actual_printed_rank_one_action]
    ext i;fin_cases i <;> simp <;> ring

theorem actual_printed_range_and_solvability (b : Fin 2 → ℝ) :
    (∃ x : Fin 2 → ℝ, R*ᵥx=b) ↔ ∃ t : ℝ, b=t • ![1,2] := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x 0+2*x 1,?_⟩
    rw [←hx,actual_printed_rank_one_action]
    ext i;fin_cases i <;> simp <;> ring
  · rintro ⟨t,rfl⟩
    refine ⟨![t,0],?_⟩
    rw [actual_printed_rank_one_action]
    ext i;fin_cases i <;> simp <;> ring

theorem actual_printed_matrix_has_rank_one : R.rank=1 := by
  have he : R=Matrix.vecMulVec (![1,2]:Fin 2→ℝ) (![1,2]:Fin 2→ℝ) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [R,Matrix.vecMulVec]
  have hu : R.rank≤1 := by rw [he];exact Matrix.rank_vecMulVec_le _ _
  have hl := Matrix.rank_submatrix_le R (fun (_:Fin 1)=>(0:Fin 2)) (fun (_:Fin 1)=>(0:Fin 2))
  have hs : R.submatrix (fun (_:Fin 1)=>(0:Fin 2)) (fun (_:Fin 1)=>(0:Fin 2))=
      (1:Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j;fin_cases i;fin_cases j;norm_num [R,Matrix.submatrix]
  rw [hs,Matrix.rank_one] at hl
  norm_num at hl
  omega

theorem actual_printed_rank_one_matrix_has_no_inverse :
    ¬∃ D : Matrix (Fin 2) (Fin 2) ℝ,D*R=1 ∧ R*D=1 := by
  rw [←actual_real_square_inverse_iff_determinant_nonzero]
  norm_num [R,Matrix.det_fin_two]

theorem actual_printed_nonzero_eigenvectors_and_actions :
    (![1,1]:Fin 2→ℝ)≠0 ∧ (![1,-1]:Fin 2→ℝ)≠0 ∧
      M*ᵥ![1,1]=3 • ![1,1] ∧ M*ᵥ![1,-1]=![1,-1] := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h;have h0:=congrFun h 0;norm_num at h0
  · intro h;have h0:=congrFun h 0;norm_num at h0
  · ext i;fin_cases i <;> norm_num [M,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · ext i;fin_cases i <;> norm_num [M,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_nonzero_homogeneous_solution_requires_zero_determinant
    {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ) (v : n → ℝ)
    (hv : v≠0) (hc : C*ᵥv=0) : C.det=0 := by
  by_contra hd
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hd hc)

theorem actual_printed_characteristic_determinant_and_roots (l : ℝ) :
    (M-l • (1:Matrix (Fin 2) (Fin 2) ℝ)).det=(2-l)^2-1 ∧
      (2-l)^2-1=(1-l)*(3-l) ∧
      ((M-l • (1:Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔ l=1 ∨ l=3) := by
  have hd : (M-l • (1:Matrix (Fin 2) (Fin 2) ℝ)).det=(1-l)*(3-l) := by
    simp [M,Matrix.det_fin_two];ring
  refine ⟨?_,by ring,?_⟩
  · rw [hd];ring
  · rw [hd,mul_eq_zero]
    constructor <;> intro h
    · rcases h with h|h <;> simp_all <;> linarith
    · rcases h with h|h <;> simp [h]

theorem actual_printed_readiness_checks :
    A*ᵥ![2,-1]=![0,-1] ∧
      ∀ x : Fin 2 → ℝ,A*ᵥx=![4,1] ↔ x=![2,1] := by
  constructor
  · rw [actual_printed_A_action];norm_num
  · intro x
    constructor
    · intro h
      rw [actual_printed_A_action] at h
      have h0:=congrFun h 0;have h1:=congrFun h 1
      simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
      ext i;fin_cases i <;> simp <;> linarith
    · intro h;rw [h,actual_printed_A_action];norm_num

end SafeLearning.CompleteFoundationsLinalgRefresher23
