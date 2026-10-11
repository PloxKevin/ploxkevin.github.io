import SafeLearning.CompleteFoundationsBook
import Mathlib.LinearAlgebra.Dimension.Finrank
import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
noncomputable section
open Set
open scoped Matrix BigOperators

namespace SafeLearning.CompleteFoundationsResidualWeightingIdentification27
open CompleteFoundationsSpectralModels (E point norm_squared_coordinates)

def rectangularH : Matrix (Fin 3) (Fin 2) ℝ := !![1,1;1,11/10;0,1]
def noisyY : Fin 3 → ℝ := ![6,31/5,21/10]
def actualResidual (z : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (rectangularH *ᵥ z-noisyY)

theorem actual_rectangular_columns_are_independent : Function.Injective rectangularH.mulVec := by
  intro x y h
  have h0 := congrArg (fun z : Fin 3 → ℝ => z 0) h
  have h2 := congrArg (fun z : Fin 3 → ℝ => z 2) h
  simp [rectangularH,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h2
  ext i
  fin_cases i
  · change x 0=y 0
    linarith
  · change x 1=y 1
    exact h2

theorem actual_noisy_reading_is_outside_the_two_dimensional_column_space :
    ¬∃z : Fin 2 → ℝ,rectangularH *ᵥ z=noisyY := by
  rintro ⟨z,h⟩
  have h0 := congrArg (fun v : Fin 3 → ℝ => v 0) h
  have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) h
  have h2 := congrArg (fun v : Fin 3 → ℝ => v 2) h
  simp [rectangularH,noisyY,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
  linarith

theorem actual_rectangular_residual_norm_is_the_sum_of_channel_squares (z : Fin 2 → ℝ) :
    ‖actualResidual z‖^2 = CompleteFoundationsBook.sensorLoss (z 0) (z 1) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [actualResidual,WithLp.toLp_apply,rectangularH,noisyY,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,CompleteFoundationsBook.sensorLoss]
  ring

theorem actual_rectangular_squared_residual_has_the_attained_unique_estimate (z : Fin 2 → ℝ) :
    ‖actualResidual ![261/67,422/201]‖^2 ≤ ‖actualResidual z‖^2 ∧
    (‖actualResidual z‖^2=‖actualResidual ![261/67,422/201]‖^2 ↔ z=![261/67,422/201]) := by
  rw [actual_rectangular_residual_norm_is_the_sum_of_channel_squares,
    actual_rectangular_residual_norm_is_the_sum_of_channel_squares]
  have h := CompleteFoundationsBook.three_sensor_unique_optimum (z 0) (z 1)
  constructor
  · exact h.1
  · change CompleteFoundationsBook.sensorLoss (z 0) (z 1)=
      CompleteFoundationsBook.sensorLoss (261/67) (422/201) ↔ z=![261/67,422/201]
    rw [h.2]
    constructor
    · rintro ⟨h0,h1⟩
      ext i
      fin_cases i <;> simp [h0,h1]
    · intro hz
      rw [hz]
      simp

theorem actual_exact_fitting_does_not_identify_the_teaching_state :
    rectangularH *ᵥ (![5,2] : Fin 2 → ℝ)=![7,36/5,2] ∧
    rectangularH *ᵥ (![4,2] : Fin 2 → ℝ)+(![1,1,0] : Fin 3 → ℝ)=![7,36/5,2] ∧
    (point 5 2 : E)≠point 4 2 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [rectangularH,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  constructor
  · ext i
    fin_cases i <;> norm_num [rectangularH,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · intro h
    have h0 := congrArg (fun x : E => x 0) h
    norm_num [point] at h0

theorem actual_row_scaling_changes_the_true_squared_residual_weights
    {J : Type*} [Fintype J] (scale residual : J → ℝ) :
    ‖(WithLp.toLp 2 (fun i => scale i*residual i) : EuclideanSpace ℝ J)‖^2 =
      ∑i,(scale i)^2*(residual i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [WithLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def unweightedCriterion (x : ℝ) : ℝ := x^2+(x-2)^2
def weightedCriterion (x : ℝ) : ℝ := 9*x^2+(x-2)^2

theorem actual_equal_weights_have_unique_minimum_one (x : ℝ) :
    unweightedCriterion 1 ≤ unweightedCriterion x ∧
    (unweightedCriterion x=unweightedCriterion 1 ↔ x=1) := by
  have he : unweightedCriterion x=unweightedCriterion 1+2*(x-1)^2 := by
    unfold unweightedCriterion
    ring
  constructor
  · nlinarith [sq_nonneg (x-1)]
  · rw [he]
    constructor <;> intro h <;> nlinarith [sq_nonneg (x-1)]

theorem actual_different_channel_weights_have_unique_minimum_one_fifth (x : ℝ) :
    weightedCriterion (1/5) ≤ weightedCriterion x ∧
    (weightedCriterion x=weightedCriterion (1/5) ↔ x=1/5) := by
  have he : weightedCriterion x=weightedCriterion (1/5)+10*(x-1/5)^2 := by
    unfold weightedCriterion
    ring
  constructor
  · nlinarith [sq_nonneg (x-1/5)]
  · rw [he]
    constructor <;> intro h <;> nlinarith [sq_nonneg (x-1/5)]

theorem actual_weight_choice_changes_the_estimate :
    (1 : ℝ)≠1/5 ∧ weightedCriterion (1/5)<weightedCriterion 1 ∧
      unweightedCriterion 1<unweightedCriterion (1/5) := by
  norm_num [weightedCriterion,unweightedCriterion]

def weakMeasurement (delta : ℝ) : E →L[ℝ] E :=
  CompleteFoundationsSpectralModels.applyMatrix !![delta,0;0,1]

theorem actual_invertible_weak_direction_has_large_state_error_with_arbitrarily_small_residual
    (epsilon M : ℝ) (hepsilon : 0<epsilon) (hM : 0<M) :
    ∃delta : ℝ,0<delta ∧ Function.Injective (weakMeasurement delta) ∧
      ‖point M 0‖=M ∧ ‖weakMeasurement delta (point M 0)‖=epsilon/2 ∧
      ‖weakMeasurement delta (point M 0)‖<epsilon := by
  let delta := epsilon/(2*M)
  have hd : 0<delta := div_pos hepsilon (mul_pos (by norm_num) hM)
  have ha (x : E) : weakMeasurement delta x=point (delta*x 0) (x 1) := by
    rw [weakMeasurement,CompleteFoundationsSpectralModels.matrix_coordinate_action]
    simp
  have hinj : Function.Injective (weakMeasurement delta) := by
    intro x y h
    rw [ha,ha] at h
    have h0 := congrArg (fun z : E => z 0) h
    have h1 := congrArg (fun z : E => z 1) h
    change delta*x 0=delta*y 0 at h0
    change x 1=y 1 at h1
    ext i
    fin_cases i
    · change x 0=y 0
      exact (mul_left_cancel₀ hd.ne' h0)
    · change x 1=y 1
      exact h1
  have hn : ‖point M 0‖=M := by
    have hs := norm_squared_coordinates (point M 0)
    change ‖point M 0‖^2=M^2+0^2 at hs
    nlinarith [norm_nonneg (point M 0)]
  have hm : delta*M=epsilon/2 := by
    dsimp [delta]
    field_simp [ne_of_gt hM]
    <;> ring
  have hnorm : ‖weakMeasurement delta (point M 0)‖=epsilon/2 := by
    rw [ha]
    change ‖point (delta*M) 0‖=epsilon/2
    rw [hm]
    have hs := norm_squared_coordinates (point (epsilon/2) 0)
    change ‖point (epsilon/2) 0‖^2=(epsilon/2)^2+0^2 at hs
    nlinarith [norm_nonneg (point (epsilon/2) 0)]
  exact ⟨delta,hd,hinj,hn,hnorm,by rw [hnorm];linarith⟩

def sumRow : Matrix (Fin 1) (Fin 2) ℝ := !![1,1]
def sumPlus : Matrix (Fin 2) (Fin 1) ℝ := !![1/2;1/2]
def moorePenrose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop :=
  A*B*A=A ∧ B*A*B=B ∧ (A*B)ᵀ=A*B ∧ (B*A)ᵀ=B*A

theorem actual_sum_row_moore_penrose_identities : moorePenrose sumRow sumPlus := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [sumRow,sumPlus,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_sum_row_pseudoinverse_is_unique (B : Matrix (Fin 2) (Fin 1) ℝ)
    (hB : moorePenrose sumRow B) : B=sumPlus := by
  have h0 := congrArg (fun M : Matrix (Fin 1) (Fin 2) ℝ => M 0 0) hB.1
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hB.2.2.2
  simp [sumRow,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sumPlus] <;> linarith

theorem actual_pseudoinverse_of_sum_six_returns_three_three :
    sumPlus *ᵥ (![6] : Fin 1 → ℝ)=![3,3] := by
  ext i
  fin_cases i <;> norm_num [sumPlus,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_sum_solution_family_has_the_printed_squared_norm (t : ℝ) :
    ‖point (3+t) (3-t)‖^2=18+2*t^2 := by
  rw [norm_squared_coordinates]
  simp [point]
  ring

theorem actual_sum_minimum_length_is_unique_but_the_measurement_does_not_identify
    (x : E) (hx : x 0+x 1=6) :
    ‖point 3 3‖ ≤ ‖x‖ ∧ (‖x‖=‖point 3 3‖ ↔ x=point 3 3) ∧
    (3 : ℝ)+3=6 ∧ (4 : ℝ)+2=6 ∧ point 3 3≠point 4 2 := by
  have h := CompleteFoundationsBook.sum_measurement_unique_minimum (x 0) (x 1) hx
  have hn := norm_squared_coordinates x
  have hp : ‖point 3 3‖^2=18 := by rw [norm_squared_coordinates];norm_num [point]
  refine ⟨?_,?_,by norm_num,by norm_num,?_⟩
  · nlinarith [norm_nonneg x,norm_nonneg (point 3 3)]
  · constructor
    · intro he
      have hh : x 0=3 ∧ x 1=3 := h.2.mp (by rw [←hn,he,hp])
      ext i
      fin_cases i <;> simp [point,hh.1,hh.2]
    · rintro rfl
      rfl
  · intro he
    have hh := congrArg (fun z : E => z 0) he
    norm_num [point] at hh


theorem actual_rectangular_column_space_has_dimension_two :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' rectangularH))=2 := by
  have hi : Function.Injective (Matrix.toLin' rectangularH) := by
    intro x y h
    apply actual_rectangular_columns_are_independent
    simpa only [Matrix.toLin'_apply] using h
  simpa using LinearMap.finrank_range_of_inj hi

theorem actual_sum_measurement_has_exactly_the_full_printed_vector_family (x : E) :
    x 0+x 1=6 ↔ ∃t : ℝ,x=point (3+t) (3-t) := by
  rw [CompleteFoundationsBook.sum_measurement_all_solutions]
  constructor
  · rintro ⟨t,h0,h1⟩
    refine ⟨t,?_⟩
    ext i
    fin_cases i <;> simp [point,h0,h1]
  · rintro ⟨t,rfl⟩
    exact ⟨t,by simp [point],by simp [point]⟩

end SafeLearning.CompleteFoundationsResidualWeightingIdentification27
