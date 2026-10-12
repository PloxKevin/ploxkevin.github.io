import SafeLearning.CompleteModulesBarrierObjective

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesBarrierPath

open CompleteModulesBarrierTraining CompleteModulesBarrierObjective

def actualBarrierPath (mu : ℝ) : ℝ := Real.sqrt (mu^2+2)-mu

def actualLinearLossBarrierObjective (mu weight : ℝ) : ℝ :=
  -weight-mu*Real.log (actualTrainingMatrix weight 1).det

theorem actual_barrier_path_stationarity_identity (mu : ℝ) :
    (actualBarrierPath mu)^2+2*mu*actualBarrierPath mu=2 := by
  have hs := Real.sq_sqrt (show 0 ≤ mu^2+2 by positivity)
  unfold actualBarrierPath
  nlinarith

theorem actual_barrier_path_is_positive (mu : ℝ) (hmu : 0 < mu) :
    0 < actualBarrierPath mu := by
  have hs := Real.sq_sqrt (show 0 ≤ mu^2+2 by positivity)
  have hn := Real.sqrt_nonneg (mu^2+2)
  unfold actualBarrierPath
  nlinarith

theorem actual_barrier_path_stays_strictly_certified (mu : ℝ) (hmu : 0 < mu) :
    (actualTrainingMatrix (actualBarrierPath mu) 1).PosDef := by
  apply actual_training_matrix_is_positive_definite
  · norm_num
  · have hp := actual_barrier_path_is_positive mu hmu
    have he := actual_barrier_path_stationarity_identity mu
    nlinarith [mul_pos hmu hp]

theorem actual_barrier_path_objective_gap (mu weight : ℝ) (hmu : 0 < mu)
    (hweight : (actualTrainingMatrix weight 1).PosDef) :
    (weight-actualBarrierPath mu)^2/(2*actualBarrierPath mu) ≤
      actualLinearLossBarrierObjective mu weight-
        actualLinearLossBarrierObjective mu (actualBarrierPath mu) := by
  have hp := actual_barrier_path_is_positive mu hmu
  have hd : 0 < 2-weight^2 := by
    simpa [actual_scalar_training_matrix_determinant] using hweight.det_pos
  have hpdet : 0 < 2-(actualBarrierPath mu)^2 := by
    simpa [actual_scalar_training_matrix_determinant] using
      (actual_barrier_path_stays_strictly_certified mu hmu).det_pos
  have he : 2-(actualBarrierPath mu)^2=2*mu*actualBarrierPath mu := by
    linarith [actual_barrier_path_stationarity_identity mu]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hd hpdet)
  rw [Real.log_div hd.ne' hpdet.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hmu.le
  have halgebra : -(weight-actualBarrierPath mu)-
      mu*((2-weight^2)/(2-(actualBarrierPath mu)^2)-1)=
      (weight-actualBarrierPath mu)^2/(2*actualBarrierPath mu) := by
    rw [he]
    field_simp
    nlinarith [actual_barrier_path_stationarity_identity mu]
  unfold actualLinearLossBarrierObjective
  simp only [actual_scalar_training_matrix_determinant,one_mul] at *
  rw [← halgebra]
  linarith

theorem actual_barrier_path_is_global_minimum (mu : ℝ) (hmu : 0 < mu) :
    IsMinOn (actualLinearLossBarrierObjective mu) actualFixedMultiplierFeasibleWeights
      (actualBarrierPath mu) := by
  intro weight hweight
  change actualLinearLossBarrierObjective mu (actualBarrierPath mu) ≤
    actualLinearLossBarrierObjective mu weight
  have h := actual_barrier_path_objective_gap mu weight hmu hweight
  have hn : 0 ≤ (weight-actualBarrierPath mu)^2/(2*actualBarrierPath mu) :=
    div_nonneg (sq_nonneg _) (by linarith [actual_barrier_path_is_positive mu hmu])
  linarith

theorem actual_barrier_path_tends_to_boundary :
    Tendsto actualBarrierPath (𝓝 0) (𝓝 (Real.sqrt 2)) := by
  have hcontinuous : Continuous actualBarrierPath := by
    unfold actualBarrierPath
    fun_prop
  simpa [ContinuousAt,actualBarrierPath] using (hcontinuous.continuousAt (x := (0:ℝ)))

theorem actual_barrier_path_determinant_tends_to_zero :
    Tendsto (fun mu : ℝ => (actualTrainingMatrix (actualBarrierPath mu) 1).det)
      (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun mu : ℝ => 2-(actualBarrierPath mu)^2) (𝓝 0)
      (𝓝 (2-(Real.sqrt 2)^2)) :=
    tendsto_const_nhds.sub (actual_barrier_path_tends_to_boundary.pow 2)
  simpa [actual_scalar_training_matrix_determinant,Real.sq_sqrt] using h

theorem actual_path_limit_is_singular_but_certified_semidefinite :
    (actualTrainingMatrix (Real.sqrt 2) 1).PosSemidef ∧
      ¬(actualTrainingMatrix (Real.sqrt 2) 1).PosDef := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (actual_training_matrix_is_symmetric _ _)
    intro vector
    change 0 ≤ vector ⬝ᵥ (actualTrainingMatrix (Real.sqrt 2) 1 *ᵥ vector)
    rw [actual_training_matrix_quadratic_identity]
    norm_num [Real.sq_sqrt]
    positivity
  · intro hpositive
    have h := hpositive.det_pos
    norm_num [actual_scalar_training_matrix_determinant,Real.sq_sqrt] at h

theorem actual_path_limit_globally_minimizes_loss_on_closed_certificate :
    ∀ weight : ℝ, (actualTrainingMatrix weight 1).PosSemidef → -Real.sqrt 2 ≤ -weight := by
  intro weight hcertified
  have hd := hcertified.det_nonneg
  simp only [actual_scalar_training_matrix_determinant,one_mul] at hd
  have hs := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem actual_fixed_interior_weight_barrier_term_vanishes
    {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ)
    (hpositive : (CompleteModulesBarrierGradient.barrierMatrix lastWeight multiplier gain firstWeight).PosDef) :
    Tendsto (fun mu : ℝ => (2*mu) • (Matrix.diagonal multiplier*
      CompleteModulesBarrierGradient.hiddenInputBlock
        ((CompleteModulesBarrierGradient.barrierMatrix lastWeight multiplier gain firstWeight)⁻¹)))
      (𝓝 0) (𝓝 (0 : Matrix K I ℝ)) := by
  have hcontinuous : Continuous (fun mu : ℝ => (2*mu) • (Matrix.diagonal multiplier*
      CompleteModulesBarrierGradient.hiddenInputBlock
        ((CompleteModulesBarrierGradient.barrierMatrix lastWeight multiplier gain firstWeight)⁻¹))) := by
    fun_prop
  simpa [ContinuousAt] using (hcontinuous.continuousAt (x := (0:ℝ)))

end SafeLearning.CompleteModulesBarrierPath
