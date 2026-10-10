import SafeLearning.CompleteModulesBarrierGradient

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesBarrierTraining

open CompleteModulesBarrierGradient
abbrev ScalarState := Fin 1 ⊕ (Fin 1 ⊕ Fin 1)

def scalarWeight (weight : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of (fun _ _ => weight)

def actualTrainingMatrix (weight multiplier : ℝ) : Matrix ScalarState ScalarState ℝ :=
  barrierMatrix (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => multiplier) 1 (scalarWeight weight)

def scalarState (input hidden output : ℝ) : ScalarState → ℝ :=
  Sum.elim (fun _ => input) (Sum.elim (fun _ => hidden) (fun _ => output))

theorem actual_training_matrix_is_symmetric (weight multiplier : ℝ) :
    (actualTrainingMatrix weight multiplier).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rcases i with i | (i|i) <;> rcases j with j | (j|j) <;>
    fin_cases i <;> fin_cases j <;>
    simp [actualTrainingMatrix,barrierMatrix,Matrix.mul_apply,Matrix.diagonal_apply,
      Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.transpose_apply] <;>
    simp [scalarWeight,Matrix.transpose,Matrix.mul_apply,Matrix.diagonal_apply,Pi.mul_apply] <;> ring

theorem actual_training_matrix_quadratic_identity (weight multiplier : ℝ)
    (vector : ScalarState → ℝ) :
    vector ⬝ᵥ (actualTrainingMatrix weight multiplier *ᵥ vector)=
      (vector (.inl 0)-multiplier*weight*vector (.inr (.inl 0)))^2+
      multiplier*(2-multiplier*weight^2)*vector (.inr (.inl 0))^2+
      vector (.inr (.inr 0))^2 := by
  simp [actualTrainingMatrix,barrierMatrix,dotProduct,Matrix.mulVec,Matrix.mul_apply,
    Fintype.sum_sum_type,Matrix.diagonal_apply,Fin.sum_univ_one,
    Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.transpose_apply]
  simp [scalarWeight,Matrix.transpose,Matrix.mul_apply,Matrix.diagonal_apply,Pi.mul_apply]
  ring

theorem actual_training_matrix_is_positive_definite (weight multiplier : ℝ)
    (hmultiplier : 0 < multiplier) (hgain : multiplier*weight^2 < 2) :
    (actualTrainingMatrix weight multiplier).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (actual_training_matrix_is_symmetric weight multiplier)
  intro vector hvector
  change 0 < vector ⬝ᵥ (actualTrainingMatrix weight multiplier *ᵥ vector)
  rw [actual_training_matrix_quadratic_identity]
  have hcoefficient : 0 < multiplier*(2-multiplier*weight^2) :=
    mul_pos hmultiplier (sub_pos.mpr hgain)
  by_cases hhidden : vector (.inr (.inl 0))=0
  · by_cases hinput : vector (.inl 0)=0
    · have houtput : vector (.inr (.inr 0)) ≠ 0 := by
        intro hz
        apply hvector
        funext i
        rcases i with i | (i|i) <;> have hi : i=0 := Subsingleton.elim _ _ <;>
          subst i <;> simp [hinput,hhidden,hz]
      rw [hhidden,hinput]
      simpa using sq_pos_of_ne_zero houtput
    · rw [hhidden]
      nlinarith [sq_pos_of_ne_zero hinput,sq_nonneg (vector (.inr (.inr 0)))]
  · have hpositive := mul_pos hcoefficient (sq_pos_of_ne_zero hhidden)
    nlinarith [sq_nonneg (vector (.inl 0)-multiplier*weight*vector (.inr (.inl 0))),
      sq_nonneg (vector (.inr (.inr 0)))]

theorem actual_joint_training_endpoints_are_feasible :
    (actualTrainingMatrix 1 1).PosDef ∧ (actualTrainingMatrix 3 (1/5)).PosDef := by
  constructor <;> apply actual_training_matrix_is_positive_definite <;> norm_num

theorem actual_joint_training_midpoint_is_infeasible :
    ¬(actualTrainingMatrix 2 (3/5)).PosDef := by
  intro hpositive
  have h := hpositive.posSemidef.dotProduct_mulVec_nonneg (scalarState (6/5) 1 0)
  change 0 ≤ scalarState (6/5) 1 0 ⬝ᵥ
    (actualTrainingMatrix 2 (3/5) *ᵥ scalarState (6/5) 1 0) at h
  rw [actual_training_matrix_quadratic_identity] at h
  norm_num [scalarState] at h

def actualJointTrainingFeasibleSet : Set (ℝ × ℝ) :=
  {parameter | (actualTrainingMatrix parameter.1 parameter.2).PosDef}

theorem actual_jointly_trained_weight_and_multiplier_set_is_not_convex :
    ¬Convex ℝ actualJointTrainingFeasibleSet := by
  intro hconvex
  have hf : (1,1) ∈ actualJointTrainingFeasibleSet := actual_joint_training_endpoints_are_feasible.1
  have hs : (3,1/5) ∈ actualJointTrainingFeasibleSet := actual_joint_training_endpoints_are_feasible.2
  have hm := hconvex hf hs (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2 : ℝ) • ((1,1) : ℝ × ℝ)+(1/2 : ℝ) • ((3,1/5) : ℝ × ℝ)=(2,3/5) := by norm_num
  rw [he] at hm
  exact actual_joint_training_midpoint_is_infeasible hm

theorem actual_finite_weight_step_can_leave_positive_definite_certificate :
    (actualTrainingMatrix 1 1).PosDef ∧ ¬(actualTrainingMatrix (1+1) 1).PosDef := by
  refine ⟨actual_joint_training_endpoints_are_feasible.1,?_⟩
  intro hpositive
  have h := hpositive.posSemidef.dotProduct_mulVec_nonneg (scalarState 2 1 0)
  change 0 ≤ scalarState 2 1 0 ⬝ᵥ (actualTrainingMatrix (1+1) 1 *ᵥ scalarState 2 1 0) at h
  rw [actual_training_matrix_quadratic_identity] at h
  norm_num [scalarState] at h

end SafeLearning.CompleteModulesBarrierTraining
