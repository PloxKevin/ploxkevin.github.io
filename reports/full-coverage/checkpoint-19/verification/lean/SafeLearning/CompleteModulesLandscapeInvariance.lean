import SafeLearning.CompleteModulesFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeInvariance

def sourceBarrier (x : ℝ) : ℝ := 4-x^2
def sourceSafeSet : Set ℝ := {x | 0 ≤ sourceBarrier x}
def unsafeCounterTrajectory (t : ℕ) : ℝ := 3*(t:ℝ)

theorem actual_source_safe_set_and_absolute_bound (x : ℝ) :
    x ∈ sourceSafeSet ↔ x ∈ Icc (-2) 2 :=
  SafeLearning.CompleteModulesFinite.landscape_safe_set x

theorem actual_source_safe_set_is_closed_interval_and_boundary_is_included :
    sourceSafeSet=Icc (-2:ℝ) 2 ∧ (-2:ℝ)∈sourceSafeSet ∧ (2:ℝ)∈sourceSafeSet := by
  refine ⟨Set.ext actual_source_safe_set_and_absolute_bound,?_,?_⟩ <;>
    norm_num [sourceSafeSet,sourceBarrier]

theorem actual_source_safe_set_is_absolute_radius_two (x : ℝ) :
    x∈sourceSafeSet ↔ |x|≤2 := by
  rw [actual_source_safe_set_and_absolute_bound,abs_le]
  rfl

theorem actual_three_printed_barrier_values_and_membership :
    sourceBarrier (-2)=0 ∧ sourceBarrier (3/2)=7/4 ∧ sourceBarrier 3= -5 ∧
    (-2:ℝ)∈sourceSafeSet ∧ (3/2:ℝ)∈sourceSafeSet ∧ (3:ℝ)∉sourceSafeSet := by
  norm_num [sourceBarrier,sourceSafeSet]

theorem actual_safe_initial_countertrajectory_leaves_at_the_first_step :
    unsafeCounterTrajectory 0=0 ∧
    (∀t,unsafeCounterTrajectory (t+1)=unsafeCounterTrajectory t+3) ∧
    unsafeCounterTrajectory 0∈sourceSafeSet ∧ unsafeCounterTrajectory 1∉sourceSafeSet := by
  refine ⟨by norm_num [unsafeCounterTrajectory],?_,?_,?_⟩
  · intro t;simp [unsafeCounterTrajectory,Nat.cast_add];ring
  all_goals norm_num [unsafeCounterTrajectory,sourceSafeSet,sourceBarrier]

theorem actual_one_step_safe_set_preservation_proves_all_horizon_safety
    (transition : ℝ→ℝ) (trajectory : ℕ→ℝ)
    (initial : trajectory 0∈sourceSafeSet)
    (recurrence : ∀t,trajectory (t+1)=transition (trajectory t))
    (preserves : ∀x∈sourceSafeSet,transition x∈sourceSafeSet) :
    ∀t,trajectory t∈sourceSafeSet := by
  intro t;induction t with
  | zero => exact initial
  | succ t ih => rw [recurrence];exact preserves _ ih

def sourceDriftStep (x : ℝ) : ℝ := x+1/100
def sourceDriftTrajectory (t : ℕ) : ℝ := (t:ℝ)/100
def sourceDriftSafeSet : Set ℝ := Iic 1

theorem actual_drift_trajectory_has_the_source_initial_state_and_recurrence :
    sourceDriftTrajectory 0=0 ∧
    ∀t,sourceDriftTrajectory (t+1)=sourceDriftStep (sourceDriftTrajectory t) := by
  refine ⟨by norm_num [sourceDriftTrajectory],?_⟩
  intro t;simp [sourceDriftTrajectory,sourceDriftStep,Nat.cast_add];ring

theorem actual_every_source_drift_recurrence_has_the_printed_formula
    (trajectory : ℕ→ℝ) (initial : trajectory 0=0)
    (recurrence : ∀t,trajectory (t+1)=sourceDriftStep (trajectory t)) :
    ∀t,trajectory t=sourceDriftTrajectory t := by
  intro t;induction t with
  | zero => simpa [sourceDriftTrajectory] using initial
  | succ t ih => rw [recurrence,ih,actual_drift_trajectory_has_the_source_initial_state_and_recurrence.2]

theorem actual_drift_safety_is_exactly_the_first_one_hundred_times (t : ℕ) :
    sourceDriftTrajectory t∈sourceDriftSafeSet ↔ t≤100 :=
  SafeLearning.CompleteModulesFinite.first_drift_violation t

theorem actual_drift_first_violation_is_one_hundred_one :
    (∀t<101,sourceDriftTrajectory t∈sourceDriftSafeSet) ∧
    sourceDriftTrajectory 100=1 ∧ sourceDriftTrajectory 101=101/100 ∧
    sourceDriftTrajectory 101∉sourceDriftSafeSet ∧
    (1:ℝ)∈sourceDriftSafeSet ∧ sourceDriftStep 1∉sourceDriftSafeSet := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro t ht;rw [actual_drift_safety_is_exactly_the_first_one_hundred_times];omega
  all_goals norm_num [sourceDriftTrajectory,sourceDriftStep,sourceDriftSafeSet]

def sourceRobustStep (x w : ℝ) : ℝ := x/2+w
def robustRadius (r : ℝ) : Prop :=
  0≤r ∧ ∀x w : ℝ,|x|≤r→|w|≤1/10→|sourceRobustStep x w|≤r

theorem actual_robust_successor_triangle_bound (r x w : ℝ)
    (hx : |x|≤r) (hw : |w|≤1/10) :
    |sourceRobustStep x w|≤r/2+1/10 := by
  have h : |sourceRobustStep x w|≤|x|/2+|w| := by
    simpa [sourceRobustStep,abs_div] using abs_add_le (x/2) w
  linarith

theorem actual_source_worst_successor_magnitude_is_attained (r : ℝ) (hr : 0≤r) :
    |r|≤r ∧ |(1/10:ℝ)|≤1/10 ∧ |sourceRobustStep r (1/10)|=r/2+1/10 := by
  have hp : 0 ≤ sourceRobustStep r (1/10) := by dsimp [sourceRobustStep];linarith
  refine ⟨by simp [abs_of_nonneg hr],by norm_num,?_⟩
  rw [abs_of_nonneg hp];rfl

theorem actual_source_robust_radius_iff (r : ℝ) : robustRadius r ↔ 1/5≤r := by
  constructor
  · rintro ⟨hr,h⟩
    have hw := actual_source_worst_successor_magnitude_is_attained r hr
    have bound := h r (1/10) hw.1 hw.2.1
    rw [hw.2.2] at bound;linarith
  · intro hr
    refine ⟨by linarith,?_⟩
    intro x w hx hw;linarith [actual_robust_successor_triangle_bound r x w hx hw]

theorem actual_one_fifth_is_the_least_robust_radius :
    IsLeast {r : ℝ | robustRadius r} (1/5) := by
  refine ⟨(actual_source_robust_radius_iff _).2 (le_refl _),?_⟩
  intro r hr;exact (actual_source_robust_radius_iff r).1 hr

theorem actual_source_robust_recurrence_has_all_horizon_safety
    (trajectory disturbance : ℕ→ℝ) (r : ℝ) (hr : 1/5≤r)
    (initial : |trajectory 0|≤r)
    (disturbance_bound : ∀t,|disturbance t|≤1/10)
    (recurrence : ∀t,trajectory (t+1)=sourceRobustStep (trajectory t) (disturbance t)) :
    ∀t,|trajectory t|≤r := by
  have preserves := ((actual_source_robust_radius_iff r).2 hr).2
  intro t;induction t with
  | zero => exact initial
  | succ t ih => rw [recurrence];exact preserves _ _ ih (disturbance_bound t)

end SafeLearning.CompleteModulesLandscapeInvariance
