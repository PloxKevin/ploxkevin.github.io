import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsPseudoinverse

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point norm_squared_coordinates inner_coordinate_formula)

def sourceA : Matrix (Fin 1) (Fin 2) ℝ := !![1,2]
def sourcePlus : Matrix (Fin 2) (Fin 1) ℝ := !![1/5;2/5]
def target : Fin 1 → ℝ := ![5]
def xStar : E := point 1 2
def nullDirection : E := point (-2) 1
def solution (t : ℝ) : E := xStar+t • nullDirection
def solves (x : E) : Prop := sourceA *ᵥ (x : Fin 2 → ℝ)=target

def moorePenrose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop :=
  A*B*A=A ∧ B*A*B=B ∧ (A*B)ᵀ=A*B ∧ (B*A)ᵀ=B*A

theorem actual_moore_penrose_identities : moorePenrose sourceA sourcePlus := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceA,sourcePlus,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_moore_penrose_unique (B : Matrix (Fin 2) (Fin 1) ℝ)
    (hB : moorePenrose sourceA B) : B=sourcePlus := by
  have h0 := congrArg (fun M : Matrix (Fin 1) (Fin 2) ℝ => M 0 0) hB.1
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hB.2.2.2
  simp [sourceA,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_succ] at h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourcePlus] <;> nlinarith

theorem actual_row_gram : sourceA*sourceAᵀ=(5 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceA,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_row_pseudoinverse_formula : sourcePlus=(1/5 : ℝ) • sourceAᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceA,sourcePlus]

theorem actual_solution_from_pseudoinverse :
    WithLp.toLp 2 (sourcePlus *ᵥ target)=xStar := by
  ext i
  fin_cases i <;> norm_num [sourcePlus,target,xStar,point,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_equation_iff (x : E) : solves x ↔ x 0+2*x 1=5 := by
  constructor
  · intro h
    have h0 := congrArg (fun y : Fin 1 → ℝ => y 0) h
    simpa [sourceA,target,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h0
  · intro h
    ext i
    fin_cases i
    simpa [sourceA,target,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h

theorem actual_null_direction : sourceA *ᵥ (nullDirection : Fin 2 → ℝ)=0 := by
  ext i
  fin_cases i
  norm_num [sourceA,nullDirection,point,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem solution_coordinates (t : ℝ) : solution t=point (1-2*t) (2+t) := by
  ext i
  fin_cases i <;> simp [solution,xStar,nullDirection,point] <;> ring

theorem actual_all_solutions (x : E) : solves x ↔ ∃ t : ℝ,x=solution t := by
  rw [actual_equation_iff]
  constructor
  · intro h
    refine ⟨x 1-2,?_⟩
    rw [solution_coordinates]
    ext i
    fin_cases i <;> simp [point] <;> linarith
  · rintro ⟨t,rfl⟩
    rw [solution_coordinates]
    simp [point]
    ring

theorem actual_orthogonality : inner ℝ xStar nullDirection=0 := by
  norm_num [inner_coordinate_formula,xStar,nullDirection,point]

theorem actual_squared_norms (t : ℝ) :
    ‖xStar‖^2=5 ∧ ‖nullDirection‖^2=5 ∧ ‖solution t‖^2=5+5*t^2 := by
  constructor
  · norm_num [norm_squared_coordinates,xStar,point]
  constructor
  · norm_num [norm_squared_coordinates,nullDirection,point]
  · rw [solution_coordinates,norm_squared_coordinates]
    simp [point]
    ring

theorem actual_unique_minimum_norm : solves xStar ∧
    ∀ x : E,solves x → ‖xStar‖ ≤ ‖x‖ ∧ (‖x‖=‖xStar‖ ↔ x=xStar) := by
  constructor
  · rw [actual_equation_iff]
    norm_num [xStar,point]
  · intro x hx
    obtain ⟨t,rfl⟩ := (actual_all_solutions x).mp hx
    have hs := actual_squared_norms t
    constructor
    · nlinarith [sq_nonneg t,norm_nonneg xStar,norm_nonneg (solution t)]
    · constructor
      · intro h
        have hsq := hs.2.2
        rw [h,hs.1] at hsq
        have ht : t=0 := by nlinarith [hsq]
        simp [solution,ht]
      · intro h
        rw [h]

theorem actual_parameter_injective : Function.Injective solution := by
  intro t u h
  have h1 := congrArg (fun x : E => x 1) h
  simp [solution_coordinates,point] at h1
  linarith

theorem actual_infinitely_many_solutions : Set.Infinite {x : E | solves x} := by
  apply (Set.infinite_range_of_injective actual_parameter_injective).mono
  rintro x ⟨t,rfl⟩
  exact (actual_all_solutions (solution t)).mpr ⟨t,rfl⟩

def rowMatrix {n : Type*} (a : n → ℝ) : Matrix (Fin 1) n ℝ := fun _ j => a j
def rowPlus {n : Type*} [Fintype n] (a : n → ℝ) : Matrix n (Fin 1) ℝ :=
  fun i _ => a i/(∑ j,a j^2)

theorem nonzero_row_squared_length_positive {n : Type*} [Fintype n]
    (a : n → ℝ) (ha : a≠0) : 0 < ∑ i,a i^2 := by
  classical
  have hw : ∃ i,a i≠0 := by
    by_contra! h
    apply ha
    ext i
    exact h i
  obtain ⟨i,hi⟩ := hw
  have hl : a i^2 ≤ ∑ j,a j^2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (a j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi) hl

theorem actual_nonzero_row_right_inverse {n : Type*} [Fintype n]
    (a : n → ℝ) (ha : a≠0) : rowMatrix a*rowPlus a=1 := by
  have hn := (nonzero_row_squared_length_positive a ha).ne'
  ext i j
  fin_cases i <;> fin_cases j
  change (∑ k,a k*(a k/(∑ j,a j^2)))=1
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  simpa only [pow_two] using div_self hn

theorem actual_nonzero_row_pseudoinverse {n : Type*} [Fintype n]
    (a : n → ℝ) (ha : a≠0) : moorePenrose (rowMatrix a) (rowPlus a) := by
  have hright := actual_nonzero_row_right_inverse a ha
  refine ⟨?_,?_,?_,?_⟩
  · rw [hright,Matrix.one_mul]
  · rw [Matrix.mul_assoc,hright,Matrix.mul_one]
  · rw [hright]
    simp
  · ext i j
    simp [rowMatrix,rowPlus,Matrix.mul_apply,Fin.sum_univ_succ]
    ring

theorem actual_general_row_formula {n : Type*} [Fintype n] (a : n → ℝ) :
    rowMatrix a*(rowMatrix a)ᵀ=(∑ i,a i^2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    rowPlus a=(∑ i,a i^2)⁻¹ • (rowMatrix a)ᵀ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    simp [rowMatrix,Matrix.mul_apply,pow_two]
  · ext i j
    simp [rowMatrix,rowPlus,div_eq_mul_inv,mul_comm]

end SafeLearning.CompleteFoundationsPseudoinverse
