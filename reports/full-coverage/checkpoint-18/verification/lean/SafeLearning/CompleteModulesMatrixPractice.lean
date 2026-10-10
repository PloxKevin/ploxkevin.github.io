import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesMatrixPractice

def actualPracticePositiveMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,2]
def actualPracticeIndefiniteMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,1]

theorem actual_source_eigendirections_are_nonzero :
    (![1,1] : Fin 2 → ℝ)≠0 ∧ (![1,-1] : Fin 2 → ℝ)≠0 := by
  constructor <;> intro h
  all_goals have he := congrFun h 0;norm_num at he

theorem actual_source_two_positive_entry_matrices :
    (∀ row column,0<actualPracticePositiveMatrix row column) ∧
    (∀ row column,0<actualPracticeIndefiniteMatrix row column) := by
  constructor <;> intro row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [actualPracticePositiveMatrix,actualPracticeIndefiniteMatrix]

theorem actual_source_two_matrices_eigenvectors :
    actualPracticePositiveMatrix*ᵥ![1,1]=3 • (![1,1] : Fin 2 → ℝ) ∧
    actualPracticePositiveMatrix*ᵥ![1,-1]=1 • (![1,-1] : Fin 2 → ℝ) ∧
    actualPracticeIndefiniteMatrix*ᵥ![1,1]=3 • (![1,1] : Fin 2 → ℝ) ∧
    actualPracticeIndefiniteMatrix*ᵥ![1,-1]=(-1) • (![1,-1] : Fin 2 → ℝ) := by
  repeat' constructor
  all_goals ext row;fin_cases row <;>
    norm_num [actualPracticePositiveMatrix,actualPracticeIndefiniteMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_two_matrices_characteristic_roots (eigenvalue : ℝ) :
    ((actualPracticePositiveMatrix-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔
      eigenvalue=3 ∨ eigenvalue=1) ∧
    ((actualPracticeIndefiniteMatrix-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔
      eigenvalue=3 ∨ eigenvalue= -1) := by
  have ha : (actualPracticePositiveMatrix-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=
      (eigenvalue-3)*(eigenvalue-1) := by
    simp [actualPracticePositiveMatrix,Matrix.det_fin_two];ring
  have hb : (actualPracticeIndefiniteMatrix-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=
      (eigenvalue-3)*(eigenvalue+1) := by
    simp [actualPracticeIndefiniteMatrix,Matrix.det_fin_two];ring
  rw [ha,hb,mul_eq_zero,mul_eq_zero]
  constructor <;> simp only [sub_eq_zero,add_eq_zero_iff_eq_neg]

theorem actual_source_positive_matrix_quadratic_identity (input : Fin 2 → ℝ) :
    input ⬝ᵥ(actualPracticePositiveMatrix*ᵥinput)=
      (input 0+input 1)^2+(input 0)^2+(input 1)^2 := by
  simp [actualPracticePositiveMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_source_positive_matrix_is_positive_definite : actualPracticePositiveMatrix.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext row column;fin_cases row <;> fin_cases column <;>
      norm_num [actualPracticePositiveMatrix,Matrix.conjTranspose_apply]
  · intro input hinput
    have he : (input 0)≠0 ∨ (input 1)≠0 := by
      by_contra h
      push Not at h
      apply hinput
      ext row;fin_cases row <;> simp [h.1,h.2]
    rw [show star input=input by simp,actual_source_positive_matrix_quadratic_identity]
    rcases he with hz | hz
    · nlinarith [sq_pos_of_ne_zero hz,sq_nonneg (input 1),sq_nonneg (input 0+input 1)]
    · nlinarith [sq_pos_of_ne_zero hz,sq_nonneg (input 0),sq_nonneg (input 0+input 1)]

theorem actual_source_indefinite_negative_direction :
    (![1,-1] : Fin 2 → ℝ) ⬝ᵥ(actualPracticeIndefiniteMatrix*ᵥ![1,-1])= -2 := by
  norm_num [actualPracticeIndefiniteMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_indefinite_positive_direction :
    (![1,1] : Fin 2 → ℝ) ⬝ᵥ(actualPracticeIndefiniteMatrix*ᵥ![1,1])=6 := by
  norm_num [actualPracticeIndefiniteMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_positive_matrix_is_positive_semidefinite :
    actualPracticePositiveMatrix.PosSemidef :=
  actual_source_positive_matrix_is_positive_definite.posSemidef

theorem actual_source_indefinite_matrix_is_not_positive_semidefinite :
    ¬actualPracticeIndefiniteMatrix.PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
  simp only [star_trivial] at hn
  rw [actual_source_indefinite_negative_direction] at hn
  norm_num at hn

def actualPracticeStableNonnormalMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,2;0,1/2]
def actualPracticeSteinStorage : Matrix (Fin 2) (Fin 2) ℝ := !![4/3,16/9;16/9,356/27]
def actualSymmetricPracticeStorage (first cross last : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![first,cross;cross,last]

theorem actual_source_nonnormal_matrix_characteristic_roots (eigenvalue : ℂ) :
    ((actualPracticeStableNonnormalMatrix.map (algebraMap ℝ ℂ)-
      eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det=0 ↔ eigenvalue=1/2) := by
  have he : (actualPracticeStableNonnormalMatrix.map (algebraMap ℝ ℂ)-
      eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det=(eigenvalue-1/2)^2 := by
    simp [actualPracticeStableNonnormalMatrix,Matrix.det_fin_two]
    ring
  rw [he,pow_eq_zero_iff (by norm_num : (2:ℕ)≠0),sub_eq_zero]

theorem actual_source_nonnormal_matrix_is_schur_stable :
    ∀ eigenvalue : ℂ,(actualPracticeStableNonnormalMatrix.map (algebraMap ℝ ℂ)-
      eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det=0 → ‖eigenvalue‖<1 := by
  intro eigenvalue he
  rw [(actual_source_nonnormal_matrix_characteristic_roots eigenvalue).mp he]
  norm_num

theorem actual_source_identity_storage_fails_decrease :
    actualPracticeStableNonnormalMatrixᵀ*actualPracticeStableNonnormalMatrix-1=
      (!![-3/4,1;1,13/4] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (![0,1] : Fin 2 → ℝ) ⬝ᵥ
      ((actualPracticeStableNonnormalMatrixᵀ*actualPracticeStableNonnormalMatrix-1)*ᵥ![0,1])=13/4 := by
  constructor
  · ext row column;fin_cases row <;> fin_cases column <;>
      norm_num [actualPracticeStableNonnormalMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  · norm_num [actualPracticeStableNonnormalMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_symmetric_stein_equation_unique_solution (first cross last : ℝ) :
    (actualPracticeStableNonnormalMatrixᵀ*actualSymmetricPracticeStorage first cross last*
      actualPracticeStableNonnormalMatrix-actualSymmetricPracticeStorage first cross last=
        -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      first=4/3 ∧ cross=16/9 ∧ last=356/27 := by
  constructor
  · intro he
    have hp := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 0 0) he
    have hq := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 0 1) he
    have hr := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 1 1) he
    norm_num [actualPracticeStableNonnormalMatrix,actualSymmetricPracticeStorage,
      Matrix.mul_apply,Fin.sum_univ_two] at hp hq hr
    constructor
    · linarith only [hp]
    · constructor <;> linarith only [hp,hq,hr]
  · rintro ⟨rfl,rfl,rfl⟩
    ext row column;fin_cases row <;> fin_cases column <;>
      norm_num [actualPracticeStableNonnormalMatrix,actualSymmetricPracticeStorage,
        Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_source_stein_storage_principal_minors :
    actualPracticeSteinStorage 0 0=4/3 ∧ actualPracticeSteinStorage.det=1168/81 ∧
      (0:ℝ)<4/3 ∧ (0:ℝ)<1168/81 := by
  norm_num [actualPracticeSteinStorage,Matrix.det_fin_two]

theorem actual_source_stein_storage_quadratic_identity (input : Fin 2 → ℝ) :
    input ⬝ᵥ(actualPracticeSteinStorage*ᵥinput)=
      (4/3)*(input 0+(4/3)*input 1)^2+(292/27)*(input 1)^2 := by
  simp [actualPracticeSteinStorage,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_source_stein_storage_is_positive_definite : actualPracticeSteinStorage.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext row column;fin_cases row <;> fin_cases column <;>
      norm_num [actualPracticeSteinStorage,Matrix.conjTranspose_apply]
  · intro input hinput
    have he : (input 0)≠0 ∨ (input 1)≠0 := by
      by_contra h
      push Not at h
      apply hinput
      ext row;fin_cases row <;> simp [h.1,h.2]
    rw [show star input=input by simp,actual_source_stein_storage_quadratic_identity]
    rcases he with hz | hz
    · by_cases hlast : input 1=0
      · simp only [hlast,mul_zero,add_zero]
        positivity
      · nlinarith [sq_nonneg (input 0+(4/3)*input 1),sq_pos_of_ne_zero hlast]
    · nlinarith [sq_nonneg (input 0+(4/3)*input 1),sq_pos_of_ne_zero hz]

theorem actual_source_weighted_energy_decreases_by_euclidean_energy (input : Fin 2 → ℝ) :
    (actualPracticeStableNonnormalMatrix*ᵥinput) ⬝ᵥ
      (actualPracticeSteinStorage*ᵥ(actualPracticeStableNonnormalMatrix*ᵥinput))-
        input ⬝ᵥ(actualPracticeSteinStorage*ᵥinput)= -((input 0)^2+(input 1)^2) := by
  simp [actualPracticeStableNonnormalMatrix,actualPracticeSteinStorage,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

end SafeLearning.CompleteModulesMatrixPractice
