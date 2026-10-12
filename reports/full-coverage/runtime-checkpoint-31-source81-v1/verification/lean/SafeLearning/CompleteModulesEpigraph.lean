import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesEpigraph

def actualSourceSchurMatrix (bound : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![bound,2;2,1]

theorem actual_source_schur_quadratic_completion (bound : ℝ) (input : Fin 2 → ℝ) :
    input ⬝ᵥ(actualSourceSchurMatrix bound*ᵥinput)=
      (bound-4)*(input 0)^2+(input 1+2*input 0)^2 := by
  simp [actualSourceSchurMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_source_schur_matrix_positive_semidefinite_iff (bound : ℝ) :
    (actualSourceSchurMatrix bound).PosSemidef ↔ 4≤bound := by
  constructor
  · intro h
    have hn := h.dotProduct_mulVec_nonneg (![1,-2] : Fin 2 → ℝ)
    simp only [star_trivial] at hn
    rw [actual_source_schur_quadratic_completion] at hn
    norm_num at hn
    linarith
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext row column;fin_cases row <;> fin_cases column <;>
        simp [actualSourceSchurMatrix,Matrix.conjTranspose_apply]
    · intro input
      rw [show star input=input by simp,actual_source_schur_quadratic_completion]
      positivity

theorem actual_source_schur_matrix_positive_definite_iff (bound : ℝ) :
    (actualSourceSchurMatrix bound).PosDef ↔ 4<bound := by
  constructor
  · intro h
    have hn := h.dotProduct_mulVec_pos (x:=(![1,-2] : Fin 2 → ℝ)) (by
      intro he;have hh:=congrFun he 0;norm_num at hh)
    simp only [star_trivial] at hn
    rw [actual_source_schur_quadratic_completion] at hn
    norm_num at hn
    linarith
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext row column;fin_cases row <;> fin_cases column <;>
        simp [actualSourceSchurMatrix,Matrix.conjTranspose_apply]
    · intro input hn
      rw [show star input=input by simp,actual_source_schur_quadratic_completion]
      by_cases hz : input 0=0
      · have hlast : input 1≠0 := by
          intro he;apply hn;ext row;fin_cases row <;> simp [hz,he]
        simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add,add_zero]
        exact sq_pos_of_ne_zero hlast
      · have hfirst : 0<(bound-4)*(input 0)^2 :=
          mul_pos (by linarith) (sq_pos_of_ne_zero hz)
        nlinarith [sq_nonneg (input 1+2*input 0)]

theorem actual_source_schur_boundary_rank_one_and_kernel :
    actualSourceSchurMatrix 4=vecMulVec (![2,1] : Fin 2 → ℝ) ![2,1] ∧
    actualSourceSchurMatrix 4*ᵥ![1,-2]=0 ∧ (actualSourceSchurMatrix 4).det=0 := by
  repeat' constructor
  · ext row column;fin_cases row <;> fin_cases column <;>
      norm_num [actualSourceSchurMatrix,vecMulVec]
  · ext row;fin_cases row <;> norm_num [actualSourceSchurMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · norm_num [actualSourceSchurMatrix,Matrix.det_fin_two]

def actualSourceEpigraphMatrix (bound first second : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![bound,first,second;first,1,0;second,0,1]

theorem actual_source_epigraph_quadratic_completion (bound first second : ℝ) (input : Fin 3 → ℝ) :
    input ⬝ᵥ(actualSourceEpigraphMatrix bound first second*ᵥinput)=
      (bound-first^2-second^2)*(input 0)^2+(input 1+first*input 0)^2+
        (input 2+second*input 0)^2 := by
  simp [actualSourceEpigraphMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

theorem actual_source_epigraph_matrix_positive_semidefinite_iff (bound first second : ℝ) :
    (actualSourceEpigraphMatrix bound first second).PosSemidef ↔ first^2+second^2≤bound := by
  constructor
  · intro h
    have hn := h.dotProduct_mulVec_nonneg (![1,-first,-second] : Fin 3 → ℝ)
    simp only [star_trivial] at hn
    rw [actual_source_epigraph_quadratic_completion] at hn
    norm_num at hn
    linarith
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext row column;fin_cases row <;> fin_cases column <;>
        simp [actualSourceEpigraphMatrix,Matrix.conjTranspose_apply]
    · intro input
      rw [show star input=input by simp,actual_source_epigraph_quadratic_completion]
      have hb : 0≤bound-first^2-second^2 := by linarith
      positivity

theorem actual_source_epigraph_matrix_positive_definite_iff (bound first second : ℝ) :
    (actualSourceEpigraphMatrix bound first second).PosDef ↔ first^2+second^2<bound := by
  constructor
  · intro h
    have hn := h.dotProduct_mulVec_pos (x:=(![1,-first,-second] : Fin 3 → ℝ)) (by
      intro he;have hh:=congrFun he 0;norm_num at hh)
    simp only [star_trivial] at hn
    rw [actual_source_epigraph_quadratic_completion] at hn
    norm_num at hn
    linarith
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext row column;fin_cases row <;> fin_cases column <;>
        simp [actualSourceEpigraphMatrix,Matrix.conjTranspose_apply]
    · intro input hn
      rw [show star input=input by simp,actual_source_epigraph_quadratic_completion]
      by_cases hz : input 0=0
      · have he : input 1≠0 ∨ input 2≠0 := by
          by_contra he;push Not at he
          apply hn;ext row;fin_cases row <;> simp [hz,he.1,he.2]
        simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add,add_zero]
        rcases he with he | he
        · nlinarith [sq_pos_of_ne_zero he,sq_nonneg (input 2)]
        · nlinarith [sq_pos_of_ne_zero he,sq_nonneg (input 1)]
      · have hp : 0<(bound-first^2-second^2)*(input 0)^2 :=
          mul_pos (by linarith) (sq_pos_of_ne_zero hz)
        nlinarith [sq_nonneg (input 1+first*input 0),sq_nonneg (input 2+second*input 0)]

theorem actual_source_epigraph_matrix_is_affine_in_unknowns
    (bound first second otherBound otherFirst otherSecond left right : ℝ) (hsum : left+right=1) :
    actualSourceEpigraphMatrix (left*bound+right*otherBound) (left*first+right*otherFirst)
      (left*second+right*otherSecond)=
        left • actualSourceEpigraphMatrix bound first second+
          right • actualSourceEpigraphMatrix otherBound otherFirst otherSecond := by
  ext row column;fin_cases row <;> fin_cases column <;>
    simp [actualSourceEpigraphMatrix] <;> linarith

theorem actual_source_epigraph_boundary_kernel (first second : ℝ) :
    actualSourceEpigraphMatrix (first^2+second^2) first second*ᵥ![1,-first,-second]=0 ∧
      (actualSourceEpigraphMatrix (first^2+second^2) first second).det=0 := by
  constructor
  · ext row;fin_cases row <;>
      simp [actualSourceEpigraphMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three];ring
  · simp [actualSourceEpigraphMatrix,Matrix.det_fin_three]
    ring

theorem actual_source_three_four_epigraph_least_bound :
    (∀ bound : ℝ,(actualSourceEpigraphMatrix bound 3 4).PosSemidef ↔ 25≤bound) ∧
    (∀ bound : ℝ,(actualSourceEpigraphMatrix bound 3 4).PosDef ↔ 25<bound) ∧
    (actualSourceEpigraphMatrix 25 3 4).PosSemidef ∧
    (actualSourceEpigraphMatrix 25 3 4).det=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro bound;rw [actual_source_epigraph_matrix_positive_semidefinite_iff];norm_num
  · intro bound;rw [actual_source_epigraph_matrix_positive_definite_iff];norm_num
  · rw [actual_source_epigraph_matrix_positive_semidefinite_iff];norm_num
  · norm_num [actualSourceEpigraphMatrix,Matrix.det_fin_three]

end SafeLearning.CompleteModulesEpigraph
