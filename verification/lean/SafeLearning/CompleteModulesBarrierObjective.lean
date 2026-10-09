import SafeLearning.CompleteModulesBarrierTraining

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesBarrierObjective

open CompleteModulesBarrierTraining CompleteModulesBarrierGradient

theorem actual_scalar_training_matrix_determinant (weight multiplier : ℝ) :
    (actualTrainingMatrix weight multiplier).det=multiplier*(2-multiplier*weight^2) := by
  letI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  unfold actualTrainingMatrix barrierMatrix
  simp only [one_pow,one_smul,Matrix.transpose_zero,neg_zero]
  rw [Matrix.det_fromBlocks₁₁]
  simp only [invOf_one,Matrix.mul_one,Matrix.det_one,one_mul]
  have he : Matrix.fromBlocks ((2:ℝ) • Matrix.diagonal (fun _ : Fin 1 => multiplier))
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) 1-
      Matrix.fromRows (-(Matrix.diagonal (fun _ : Fin 1 => multiplier)*scalarWeight weight)) 0*
      Matrix.fromCols (-((scalarWeight weight)ᵀ*Matrix.diagonal (fun _ : Fin 1 => multiplier))) 0=
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 1 => multiplier*(2-multiplier*weight^2)))
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromRows_mul_fromCols,Matrix.mul_apply,Matrix.diagonal_apply] <;>
      simp [scalarWeight,Matrix.transpose] <;> ring
  rw [he,Matrix.det_fromBlocks_zero₂₁]
  simp

def examplePolynomialObjective (weight : ℝ) : ℝ :=
  (weight^2-1)^2+weight^3/3-weight

def exampleTrainingLoss (weight : ℝ) : ℝ :=
  examplePolynomialObjective weight+Real.log (actualTrainingMatrix weight 1).det

def exampleBarrierObjective (weight : ℝ) : ℝ :=
  exampleTrainingLoss weight-Real.log (actualTrainingMatrix weight 1).det

def actualFixedMultiplierFeasibleWeights : Set ℝ :=
  {weight | (actualTrainingMatrix weight 1).PosDef}

theorem actual_example_barrier_objective_is_polynomial (weight : ℝ) :
    exampleBarrierObjective weight=examplePolynomialObjective weight := by
  simp [exampleBarrierObjective,exampleTrainingLoss]

theorem actual_polynomial_objective_gap (weight : ℝ) :
    examplePolynomialObjective weight-examplePolynomialObjective (-1)=
      (weight+1)^2*((weight-1)^2+(weight-2)/3) := by
  unfold examplePolynomialObjective
  ring

theorem actual_polynomial_negative_halfline_minimum (weight : ℝ) (hweight : weight ≤ 0) :
    examplePolynomialObjective (-1) ≤ examplePolynomialObjective weight := by
  apply sub_nonneg.mp
  rw [actual_polynomial_objective_gap]
  apply mul_nonneg (sq_nonneg _)
  nlinarith [sq_nonneg weight]

theorem actual_barrier_objective_has_feasible_nonglobal_local_minimum :
    (-1:ℝ) ∈ actualFixedMultiplierFeasibleWeights ∧
      IsLocalMinOn exampleBarrierObjective actualFixedMultiplierFeasibleWeights (-1) ∧
      ¬IsMinOn exampleBarrierObjective actualFixedMultiplierFeasibleWeights (-1) := by
  have hminus : (-1:ℝ) ∈ actualFixedMultiplierFeasibleWeights := by
    apply actual_training_matrix_is_positive_definite <;> norm_num
  have hplus : (1:ℝ) ∈ actualFixedMultiplierFeasibleWeights := actual_joint_training_endpoints_are_feasible.1
  have hlocal : IsLocalMin exampleBarrierObjective (-1) := by
    filter_upwards [eventually_lt_nhds (show (-1:ℝ)<0 by norm_num)] with weight hweight
    simp only [actual_example_barrier_objective_is_polynomial]
    exact actual_polynomial_negative_halfline_minimum weight hweight.le
  refine ⟨hminus,hlocal.isLocalMinOn actualFixedMultiplierFeasibleWeights,?_⟩
  intro hglobal
  have h := hglobal hplus
  norm_num [actual_example_barrier_objective_is_polynomial,examplePolynomialObjective] at h

theorem actual_training_loss_is_not_convex_on_certified_weights :
    ¬ConvexOn ℝ actualFixedMultiplierFeasibleWeights exampleTrainingLoss := by
  intro hconvex
  have hminus : (-1:ℝ) ∈ actualFixedMultiplierFeasibleWeights := by
    apply actual_training_matrix_is_positive_definite <;> norm_num
  have hplus : (1:ℝ) ∈ actualFixedMultiplierFeasibleWeights := actual_joint_training_endpoints_are_feasible.1
  have h := hconvex.2 hminus hplus
    (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num)
    (show (1/2:ℝ)+(1/2:ℝ)=1 by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  norm_num [exampleTrainingLoss,examplePolynomialObjective,actual_scalar_training_matrix_determinant] at h
  linarith

end SafeLearning.CompleteModulesBarrierObjective
