import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SafeLearning.CompleteFoundationsCholeskyFamily
open scoped BigOperators
open Matrix

def sourceP (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,2,0;2,5,2;0,2,a]
def sourceL (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0;2,1,0;0,2,Real.sqrt (a-4)]

theorem actual_source_matrix_hermitian (a : ℝ) : (sourceP a).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceP,Matrix.conjTranspose_apply]

theorem actual_source_quadratic_completion (a : ℝ) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (sourceP a *ᵥ x) =
      (x 0+2*x 1)^2+(x 1+2*x 2)^2+(a-4)*(x 2)^2 := by
  simp [sourceP,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_source_positive_definite_iff (a : ℝ) :
    (sourceP a).PosDef ↔ 4 < a := by
  constructor
  · intro h
    have hn : (![4,-2,1] : Fin 3 → ℝ) ≠ 0 := by
      intro he; have hh := congrFun he 2; norm_num at hh
    have hp := h.dotProduct_mulVec_pos hn
    simp only [star_trivial] at *
    rw [actual_source_quadratic_completion] at hp
    norm_num at hp
    linarith
  · intro ha
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (actual_source_matrix_hermitian a)
    intro x hx
    simp only [star_trivial] at *
    rw [actual_source_quadratic_completion]
    by_cases h2 : x 2 = 0
    · by_cases h1 : x 1 = 0
      · have h0 : x 0 ≠ 0 := by
          intro he; apply hx; ext i; fin_cases i <;> simp [he,h1,h2]
        simp only [h1,h2,mul_zero,add_zero,zero_pow (by norm_num : 2 ≠ 0)]
        simpa using sq_pos_of_ne_zero h0
      · have hs := sq_pos_of_ne_zero h1
        simp only [h2,mul_zero,add_zero,zero_pow (by norm_num : 2 ≠ 0)]
        nlinarith [sq_nonneg (x 0+2*x 1)]
    · have hs := mul_pos (sub_pos.mpr ha) (sq_pos_of_ne_zero h2)
      nlinarith [sq_nonneg (x 0+2*x 1),sq_nonneg (x 1+2*x 2)]

theorem actual_source_positive_semidefinite_iff (a : ℝ) :
    (sourceP a).PosSemidef ↔ 4 ≤ a := by
  constructor
  · intro h
    have hp := h.dotProduct_mulVec_nonneg (![4,-2,1] : Fin 3 → ℝ)
    simp only [star_trivial] at *
    rw [actual_source_quadratic_completion] at hp
    norm_num at hp
    linarith
  · intro ha
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (actual_source_matrix_hermitian a)
    intro x
    simp only [star_trivial] at *
    rw [actual_source_quadratic_completion]
    positivity

theorem actual_source_cholesky_matrix_identity (a : ℝ) (ha : 4 ≤ a) :
    sourceP a = sourceL a * (sourceL a).transpose := by
  have hs : (Real.sqrt (a-4))^2 = a-4 := Real.sq_sqrt (sub_nonneg.mpr ha)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceP,sourceL,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]
  all_goals nlinarith [hs]

theorem actual_source_cholesky_lower_triangular (a : ℝ) :
    (sourceL a).IsLowerTriangular := by
  change ∀ ⦃i j : Fin 3⦄, i < j → sourceL a i j = 0
  intro i j hji
  fin_cases i <;> fin_cases j <;> norm_num at hji <;> norm_num [sourceL]

theorem actual_source_symbolic_pivots (a : ℝ) (ha : 4 ≤ a) :
    sourceL a 0 0 = 1 ∧ sourceL a 1 0 = 2 ∧ sourceL a 2 0 = 0 ∧
    sourceL a 1 1 = Real.sqrt (5-4) ∧ sourceL a 1 1 = 1 ∧
    sourceL a 2 1 = 2 ∧ (sourceL a 2 2)^2 = a-4 := by
  norm_num [sourceL,Real.sq_sqrt (sub_nonneg.mpr ha)]

theorem actual_source_cholesky_positive_diagonal_iff (a : ℝ) :
    (∀ j,0 < sourceL a j j) ↔ 4 < a := by
  constructor
  · intro h
    have hs := h 2
    simpa [sourceL,Real.sqrt_pos] using hs
  · intro ha
    intro j
    fin_cases j <;> simp [sourceL,Real.sqrt_pos,sub_pos.mpr ha]

theorem actual_source_leading_principal_minors (a : ℝ) :
    sourceP a 0 0 = 1 ∧
    ((sourceP a).submatrix Fin.castSucc Fin.castSucc : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∧
    (sourceP a).det = (5*a-4)-4*a ∧ (sourceP a).det = a-4 := by
  norm_num [sourceP,Matrix.det_fin_two,Matrix.det_fin_three]
  ring

theorem actual_source_four_psd_singular_and_actual_null_vector :
    (sourceP 4).PosSemidef ∧ (sourceP 4).det = 0 ∧
    (![4,-2,1] : Fin 3 → ℝ) ≠ 0 ∧
    (sourceL 4).transpose *ᵥ ![4,-2,1] = 0 ∧
    sourceP 4 *ᵥ ![4,-2,1] = 0 ∧ sourceL 4 2 2 = 0 := by
  refine ⟨(actual_source_positive_semidefinite_iff 4).mpr (by norm_num),?_,?_,?_,?_,?_⟩
  · norm_num [actual_source_leading_principal_minors]
  · intro he; have h := congrFun he 2; norm_num at h
  · ext i; fin_cases i <;> norm_num [sourceL,Matrix.transpose_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · ext i; fin_cases i <;> norm_num [sourceP,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · norm_num [sourceL]

theorem actual_source_five_exact_factor :
    sourceL 5 = !![1,0,0;2,1,0;0,2,1] ∧
    sourceP 5 = sourceL 5 * (sourceL 5).transpose := by
  exact ⟨by norm_num [sourceL],actual_source_cholesky_matrix_identity 5 (by norm_num)⟩

theorem actual_source_forward_solve_unique (y : Fin 3 → ℝ) :
    sourceL 5 *ᵥ y = ![1,4,5] ↔ y = ![1,2,1] := by
  constructor
  · intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    norm_num [sourceL,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
    ext i; fin_cases i <;> norm_num <;> linarith
  · intro he; subst y
    ext i; fin_cases i <;> norm_num [sourceL,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_source_backward_solve_unique (x : Fin 3 → ℝ) :
    (sourceL 5).transpose *ᵥ x = ![1,2,1] ↔ x = ![1,0,1] := by
  constructor
  · intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    norm_num [sourceL,Matrix.transpose_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
    ext i; fin_cases i <;> norm_num <;> linarith
  · intro he; subst x
    ext i; fin_cases i <;> norm_num [sourceL,Matrix.transpose_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_source_original_solution : sourceP 5 *ᵥ ![1,0,1] = ![1,4,5] := by
  ext i; fin_cases i <;> norm_num [sourceP,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_source_five_log_determinant :
    (sourceP 5).det = 1 ∧ Real.log (sourceP 5).det = 0 ∧
    Real.log (sourceP 5).det = 2 * ∑ j,Real.log (sourceL 5 j j) := by
  have hd : (sourceP 5).det = 1 := by
    norm_num [sourceP,Matrix.det_fin_three]
  norm_num [hd,sourceL,Fin.sum_univ_succ]

end SafeLearning.CompleteFoundationsCholeskyFamily
