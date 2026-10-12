import SafeLearning.CompleteAppliedMultiplierLoop

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedMultiplierEnvelope
open SafeLearning.CompleteAppliedMultiplierLoop
open SafeLearning.CompleteDualPILinearModel
open SafeLearning.CompleteDualPIStability
open SafeLearning.CompleteDualPIOscillation

def sourceTrajectory (c kp ki : ℝ) (initial : ℝ×ℝ) : ℕ→ℝ×ℝ
  | 0 => initial
  | n+1 => loopStep 1 c kp ki (sourceTrajectory c kp ki initial n).1
      (sourceTrajectory c kp ki initial n).2
def numericEnergy (state : ℝ×ℝ) : ℝ := state.1^2+(state.1+state.2)^2
def numericEnvelope (state : ℝ×ℝ) : ℝ := Real.sqrt (numericEnergy state)

theorem actual_source_trajectory_exists_and_is_unique (c kp ki : ℝ)
    (initial : ℝ×ℝ) (state : ℕ→ℝ×ℝ) (h0 : state 0=initial)
    (hrec : ∀n,state (n+1)=loopStep 1 c kp ki (state n).1 (state n).2) :
    state=sourceTrajectory c kp ki initial := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hrec,sourceTrajectory,ih]

theorem actual_gain_one_pure_matrix_period_is_exactly_six (n : ℕ)
    (hn : 1≤n) (hsmall : n<6) : (sourceMatrix 1 0 1)^n≠1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ=>M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ=>M 0 1) h
  interval_cases n <;>
    norm_num [sourceMatrix,loopMatrix,pow_succ,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.one_apply] at *

theorem actual_every_nonzero_pure_loop_state_has_a_nondecaying_trajectory
    (c ki : ℝ) (hgain : 0<c*ki ∧ c*ki<4) (initial : ℝ×ℝ)
    (hi : initial.1≠0 ∨ initial.2≠0) :
    ¬(Tendsto (fun n=>(sourceTrajectory c 0 ki initial n).1) atTop (𝓝 0) ∧
      Tendsto (fun n=>(sourceTrajectory c 0 ki initial n).2) atTop (𝓝 0)) := by
  apply actual_nonzero_pure_trajectory_does_not_decay_to_origin (c*ki) hgain
    (sourceTrajectory c 0 ki initial)
  · intro n
    simp [sourceTrajectory,loopStep]
  · exact hi

theorem actual_zero_initial_pure_loop_is_the_constant_equilibrium
    (c ki : ℝ) (n : ℕ) : sourceTrajectory c 0 ki (0,0) n=(0,0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sourceTrajectory,ih,loopStep]

theorem actual_numeric_energy_is_positive_except_at_the_equilibrium (state : ℝ×ℝ) :
    0≤numericEnergy state ∧ (numericEnergy state=0 ↔ state=(0,0)) := by
  unfold numericEnergy
  refine ⟨by positivity,?_⟩
  constructor
  · intro h
    have h1 : state.1=0 := by nlinarith [sq_nonneg (state.1+state.2)]
    have h2 : state.2=0 := by nlinarith [sq_nonneg state.1]
    exact Prod.ext h1 h2
  · rintro rfl
    norm_num

theorem actual_numeric_step_halves_the_true_energy (state : ℝ×ℝ) :
    numericEnergy (loopStep 1 1 (1/2) (1/2) state.1 state.2)=
      (1/2)*numericEnergy state := by
  unfold numericEnergy loopStep
  ring

theorem actual_every_numeric_source_trajectory_has_the_exact_energy_and_envelope
    (state : ℕ→ℝ×ℝ)
    (hrec : ∀n,state (n+1)=loopStep 1 1 (1/2) (1/2) (state n).1 (state n).2)
    (n : ℕ) :
    numericEnergy (state n)=(1/2:ℝ)^n*numericEnergy (state 0) ∧
      numericEnvelope (state n)=(Real.sqrt (1/2:ℝ))^n*numericEnvelope (state 0) := by
  have he (n : ℕ) : numericEnergy (state n)=(1/2:ℝ)^n*numericEnergy (state 0) := by
    induction n with
    | zero => simp
    | succ n ih => rw [hrec,actual_numeric_step_halves_the_true_energy,ih,pow_succ];ring
  refine ⟨he n,?_⟩
  have hstep (k : ℕ) : numericEnvelope (state (k+1))=
      Real.sqrt (1/2:ℝ)*numericEnvelope (state k) := by
    unfold numericEnvelope
    rw [hrec,actual_numeric_step_halves_the_true_energy,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤1/2)]
  induction n with
  | zero => simp
  | succ n ih => rw [hstep,ih,pow_succ];ring

theorem actual_every_numeric_source_trajectory_has_the_eight_step_cycle
    (state : ℕ→ℝ×ℝ)
    (hrec : ∀n,state (n+1)=loopStep 1 1 (1/2) (1/2) (state n).1 (state n).2)
    (n : ℕ) : state (n+8)=((state n).1/16,(state n).2/16) := by
  rw [show n+8=n+7+1 by omega,hrec,
    show n+7=n+6+1 by omega,hrec,
    show n+6=n+5+1 by omega,hrec,
    show n+5=n+4+1 by omega,hrec,
    show n+4=n+3+1 by omega,hrec,
    show n+3=n+2+1 by omega,hrec,
    show n+2=n+1+1 by omega,hrec,hrec n]
  apply Prod.ext <;> simp [loopStep] <;> ring

theorem actual_every_numeric_source_trajectory_decays_to_the_origin
    (state : ℕ→ℝ×ℝ)
    (hrec : ∀n,state (n+1)=loopStep 1 1 (1/2) (1/2) (state n).1 (state n).2) :
    Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
      Tendsto (fun n=>(state n).2) atTop (𝓝 0) := by
  exact (actual_all_source_uncurved_trajectories_decay_iff_gain_region
    1 (1/2) (1/2)).mpr (by norm_num) state hrec

end SafeLearning.CompleteAppliedMultiplierEnvelope
