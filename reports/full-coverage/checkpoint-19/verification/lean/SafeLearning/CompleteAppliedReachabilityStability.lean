import SafeLearning.CompleteAppliedReachabilityCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedReachabilityStability
open CompleteAppliedReachabilityCoordinates

theorem actual_unforced_source_recurrence_is_unique
    (x : ℕ→E) (hnext : ∀n,x (n+1)=step (x n) 0) :
    ∀n,x n=zeroInputTrajectory (x 0) n := by
  intro n;induction n with
  | zero => exact (actual_zero_input_trajectory_initial_and_recurrence (x 0)).1.symm
  | succ n ih => rw [hnext,ih,(actual_zero_input_trajectory_initial_and_recurrence (x 0)).2]

theorem actual_all_horizon_unforced_trajectory_norm_never_increases (initial : E) (n : ℕ) :
    ‖zeroInputTrajectory initial n‖≤‖initial‖ := by
  have hh : (1/2:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq : (1/4:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hh0 : 0≤(1/2:ℝ)^n := pow_nonneg (by norm_num) _
  have hq0 : 0≤(1/4:ℝ)^n := pow_nonneg (by norm_num) _
  have hh2 : ((1/2:ℝ)^n)^2≤1 := by nlinarith
  have hq2 : ((1/4:ℝ)^n)^2≤1 := by nlinarith
  have h0 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg (initial 0))
  have h1 := mul_le_mul_of_nonneg_right hq2 (sq_nonneg (initial 1))
  have hs : ‖zeroInputTrajectory initial n‖^2≤‖initial‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two,zeroInputTrajectory,point,WithLp.ofLp_toLp,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_zero]
    simp only [mul_pow]
    nlinarith
  nlinarith [norm_nonneg (zeroInputTrajectory initial n),norm_nonneg initial]

def originLyapunovStable : Prop :=
  ∀ε:ℝ,0<ε→∃δ:ℝ,0<δ∧∀x:ℕ→E,
    (∀n,x (n+1)=step (x n) 0)→‖x 0‖<δ→∀n,‖x n‖<ε

theorem actual_source_unforced_origin_is_lyapunov_stable : originLyapunovStable := by
  intro ε hε
  refine ⟨ε,hε,?_⟩
  intro x hnext h0 n
  rw [actual_unforced_source_recurrence_is_unique x hnext n]
  exact (actual_all_horizon_unforced_trajectory_norm_never_increases (x 0) n).trans_lt h0

theorem actual_every_unforced_source_recurrence_converges_to_zero
    (x : ℕ→E) (hnext : ∀n,x (n+1)=step (x n) 0) : Tendsto x atTop (𝓝 0) := by
  have he : x=zeroInputTrajectory (x 0) := funext (actual_unforced_source_recurrence_is_unique x hnext)
  rw [he]
  exact actual_stable_unforced_dynamics_have_every_initial_trajectory_converging _

theorem actual_stability_and_attraction_do_not_imply_controllability :
    originLyapunovStable ∧
    (∀x:ℕ→E,(∀n,x (n+1)=step (x n) 0)→Tendsto x atTop (𝓝 0)) ∧
    ¬∀target:E,target∈reachableFromZero :=
  ⟨actual_source_unforced_origin_is_lyapunov_stable,
    actual_every_unforced_source_recurrence_converges_to_zero,
    actual_source_system_is_not_controllable_from_zero⟩

end SafeLearning.CompleteAppliedReachabilityStability
