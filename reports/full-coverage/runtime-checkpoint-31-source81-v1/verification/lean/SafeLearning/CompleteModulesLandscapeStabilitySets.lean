import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesLandscapeStabilitySets

def sourceStep (x : ℝ) : ℝ := x/2
def sourceTrajectory (initial : ℝ) (time : ℕ) : ℝ := (1/2:ℝ)^time*initial

theorem actual_half_step_interval_image (left right : ℝ) :
    sourceStep '' Icc left right=Icc (left/2) (right/2) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change left/2 ≤ x/2 ∧ x/2 ≤ right/2
    constructor <;> linarith [hx.1,hx.2]
  · rintro ⟨hl,hr⟩
    refine ⟨2*y,⟨by linarith,by linarith⟩,?_⟩
    simp [sourceStep]

theorem actual_first_constraint_is_one_step_invariant_and_second_is_not :
    sourceStep '' Icc (-1:ℝ) 1=Icc (-1/2:ℝ) (1/2) ∧
    sourceStep '' Icc (-1:ℝ) 1 ⊆ Icc (-1:ℝ) 1 ∧
    sourceStep '' Icc (1:ℝ) 2=Icc (1/2:ℝ) 1 ∧
    ¬sourceStep '' Icc (1:ℝ) 2 ⊆ Icc (1:ℝ) 2 := by
  refine ⟨by simpa using actual_half_step_interval_image (-1) 1,?_,
    by simpa using actual_half_step_interval_image 1 2,?_⟩
  · rw [actual_half_step_interval_image]
    intro y hy;constructor <;> linarith [hy.1,hy.2]
  · intro h
    have hv : sourceStep 1∈sourceStep '' Icc (1:ℝ) 2 := ⟨1,by norm_num,rfl⟩
    have hb := h hv
    norm_num [sourceStep] at hb

theorem actual_source_trajectory_initial_value_and_recurrence (initial : ℝ) (time : ℕ) :
    sourceTrajectory initial 0=initial ∧
    sourceTrajectory initial (time+1)=sourceStep (sourceTrajectory initial time) := by
  constructor
  · simp [sourceTrajectory]
  · simp [sourceTrajectory,sourceStep,pow_succ]
    ring

theorem actual_any_source_recurrence_has_the_stated_trajectory
    (trajectory : ℕ → ℝ) (initial : ℝ) (h0 : trajectory 0=initial)
    (hstep : ∀ t,trajectory (t+1)=sourceStep (trajectory t)) (time : ℕ) :
    trajectory time=sourceTrajectory initial time := by
  induction time with
  | zero => simpa [sourceTrajectory] using h0
  | succ t ih => rw [hstep,ih,(actual_source_trajectory_initial_value_and_recurrence initial t).2]

theorem actual_all_source_trajectories_converge_to_the_zero_equilibrium (initial : ℝ) :
    sourceStep 0=0 ∧ Tendsto (sourceTrajectory initial) atTop (𝓝 0) := by
  constructor
  · simp [sourceStep]
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const initial
    change Tendsto (fun t : ℕ => (1/2:ℝ)^t*initial) atTop (𝓝 0)
    simpa only [zero_mul] using h

theorem actual_first_constraint_induction_for_every_allowed_initial
    (trajectory : ℕ → ℝ) (h0 : trajectory 0∈Icc (-1:ℝ) 1)
    (hstep : ∀ t,trajectory (t+1)=sourceStep (trajectory t)) (time : ℕ) :
    trajectory time∈Icc (-1:ℝ) 1 := by
  induction time with
  | zero => exact h0
  | succ t ih =>
    rw [hstep]
    have hb := actual_first_constraint_is_one_step_invariant_and_second_is_not.2.1
    exact hb ⟨trajectory t,ih,rfl⟩

theorem actual_source_initial_two_converges_but_fails_both_constraint_guarantees :
    Tendsto (sourceTrajectory 2) atTop (𝓝 0) ∧
    sourceTrajectory 2 0∉Icc (-1:ℝ) 1 ∧
    sourceTrajectory 2 0∈Icc (1:ℝ) 2 ∧
    sourceTrajectory 2 2∉Icc (1:ℝ) 2 ∧
    sourceTrajectory 1 0∈Icc (1:ℝ) 2 ∧
    sourceTrajectory 1 1∉Icc (1:ℝ) 2 := by
  refine ⟨(actual_all_source_trajectories_converge_to_the_zero_equilibrium 2).2,?_,?_,?_,?_,?_⟩
  all_goals norm_num [sourceTrajectory]

theorem actual_source_initial_two_literal_integer_power (time : ℕ) :
    sourceTrajectory 2 time=(2:ℝ)^((1:ℤ)-(time:ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (2:ℝ)≠0)]
  simp [sourceTrajectory,one_div,zpow_natCast,inv_pow,div_eq_mul_inv]
  ring

end SafeLearning.CompleteModulesLandscapeStabilitySets
