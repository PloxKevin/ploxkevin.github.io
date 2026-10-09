import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteModulesScalarLyapunov

def actualSourceScalarStorage (weight input : ℝ) : ℝ := weight*input^2
def actualSourceScalarTrajectory (initial : ℝ) (time : ℕ) : ℝ := (4/5:ℝ)^time*initial

theorem actual_source_scalar_lyapunov_normalization_unique (weight : ℝ) :
    (4/5:ℝ)^2*weight-weight= -1 ↔ weight=25/9 := by
  constructor <;> intro h <;> nlinarith

theorem actual_source_scalar_weight_decimal_rounding :
    (0:ℝ)<25/9 ∧ |(25/9:ℝ)-277778/100000|<1/200000 := by
  norm_num

theorem actual_source_scalar_storage_is_positive_definite (weight : ℝ) (hweight : 0<weight) :
    actualSourceScalarStorage weight 0=0 ∧
      ∀ input : ℝ,input≠0 → 0<actualSourceScalarStorage weight input := by
  constructor
  · simp [actualSourceScalarStorage]
  · intro input hinput
    exact mul_pos hweight (sq_pos_of_ne_zero hinput)

theorem actual_source_scalar_storage_difference (weight input : ℝ) :
    actualSourceScalarStorage weight ((4/5)*input)-actualSourceScalarStorage weight input=
      (-9/25)*weight*input^2 := by
  unfold actualSourceScalarStorage
  ring

theorem actual_source_normalized_storage_decreases_by_square (input : ℝ) :
    actualSourceScalarStorage (25/9) ((4/5)*input)-actualSourceScalarStorage (25/9) input= -input^2 := by
  rw [actual_source_scalar_storage_difference]
  ring

theorem actual_every_positive_source_weight_gives_strict_decrease
    (weight input : ℝ) (hweight : 0<weight) (hinput : input≠0) :
    (4/5:ℝ)^2*weight-weight<0 ∧
    actualSourceScalarStorage weight ((4/5)*input)<actualSourceScalarStorage weight input := by
  constructor
  · nlinarith
  · have hd := actual_source_scalar_storage_difference weight input
    have hs := sq_pos_of_ne_zero hinput
    have hp : 0<weight*input^2 := mul_pos hweight hs
    linarith

theorem actual_source_geometric_trajectory_recursion (initial : ℝ) :
    actualSourceScalarTrajectory initial 0=initial ∧
      ∀ time,actualSourceScalarTrajectory initial (time+1)=(4/5)*actualSourceScalarTrajectory initial time := by
  constructor
  · simp [actualSourceScalarTrajectory]
  · intro time
    simp [actualSourceScalarTrajectory,pow_succ]
    ring

theorem actual_every_source_trajectory_is_the_true_geometric_trajectory
    (state : ℕ → ℝ) (hrecursion : ∀ time,state (time+1)=(4/5)*state time) :
    ∀ time,state time=actualSourceScalarTrajectory (state 0) time := by
  intro time
  induction time with
  | zero => simp [actualSourceScalarTrajectory]
  | succ time ih =>
    rw [hrecursion,ih,(actual_source_geometric_trajectory_recursion (state 0)).2]

theorem actual_source_trajectories_converge_to_zero (initial : ℝ) :
    Tendsto (actualSourceScalarTrajectory initial) atTop (𝓝 0) := by
  have hp : Tendsto (fun time : ℕ => (4/5:ℝ)^time) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun time : ℕ => (4/5:ℝ)^time*initial) atTop (𝓝 0)
  simpa only [zero_mul] using hp.mul_const initial

theorem actual_source_origin_is_lyapunov_stable (radius : ℝ) (hradius : 0<radius) :
    ∃ initialRadius : ℝ,0 < initialRadius ∧
      ∀ initial : ℝ,|initial| < initialRadius → ∀ time,|actualSourceScalarTrajectory initial time|<radius := by
  refine ⟨radius,hradius,?_⟩
  intro initial hinitial time
  unfold actualSourceScalarTrajectory
  rw [abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤4/5) time)]
  have hp : (4/5:ℝ)^time≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb := mul_le_mul_of_nonneg_right hp (abs_nonneg initial)
  linarith

theorem actual_source_unstable_factor_forbids_positive_storage_decrease
    (weight : ℝ) (hweight : 0<weight) :
    (11/10:ℝ)^2*weight-weight=(21/100)*weight ∧
      0<(11/10:ℝ)^2*weight-weight ∧
      ¬((11/10:ℝ)^2*weight-weight<0) := by
  constructor
  · ring
  · constructor <;> nlinarith

end SafeLearning.CompleteModulesScalarLyapunov
