import Mathlib

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompletePredictiveSafety

def X : Set ℝ := Icc (-1) 1
def U : Set ℝ := Icc (-1 / 2) (1 / 2)
def terminalPlan (x u v : ℝ) : Prop :=
  x ∈ X ∧ u ∈ U ∧ v ∈ U ∧ x + u ∈ X ∧ x + u + v = 0

theorem terminal_zero_controller : (0 : ℝ) ∈ X ∧ (0 : ℝ) ∈ U ∧ 0 + 0 = (0 : ℝ) := by
  norm_num [X, U]

theorem terminal_plan_feasible_iff (x : ℝ) :
    (∃ u v, terminalPlan x u v) ↔ x ∈ X := by
  constructor
  · rintro ⟨u, v, hp⟩
    exact hp.1
  · intro hx
    refine ⟨-x / 2, -x / 2, hx, ?_, ?_, ?_, ?_⟩
    · unfold U
      constructor <;> linarith [hx.1, hx.2]
    · unfold U
      constructor <;> linarith [hx.1, hx.2]
    · unfold X
      constructor <;> linarith [hx.1, hx.2]
    · ring

theorem exact_terminal_shift (x u v : ℝ) (hp : terminalPlan x u v) :
    terminalPlan (x + u) v 0 := by
  refine ⟨hp.2.2.2.1, hp.2.2.1, by norm_num [U], ?_, ?_⟩
  · rw [hp.2.2.2.2]
    norm_num [X]
  · linarith [hp.2.2.2.2]

theorem unique_plan_at_one (u v : ℝ) :
    terminalPlan 1 u v ↔ u = -1 / 2 ∧ v = -1 / 2 := by
  constructor
  · intro hp
    have hu := hp.2.1.1
    have hv := hp.2.2.1.1
    have ht := hp.2.2.2.2
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [terminalPlan, X, U]

theorem feasible_first_input_at_half (u : ℝ) :
    (∃ v, terminalPlan (1 / 2) u v) ↔ u ∈ Icc (-1 / 2) 0 := by
  constructor
  · rintro ⟨v, hp⟩
    refine ⟨hp.2.1.1, ?_⟩
    linarith [hp.2.2.1.1, hp.2.2.2.2]
  · intro hu
    refine ⟨-1 / 2 - u, ?_⟩
    unfold terminalPlan X U
    refine ⟨by norm_num, ⟨hu.1, by linarith [hu.2]⟩,
      ⟨by linarith [hu.2], by linarith [hu.1]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩, by ring⟩

theorem half_nearest_first_input (u v : ℝ) (hp : terminalPlan (1 / 2) u v) :
    |1 / 2 - (0 : ℝ)| ≤ |1 / 2 - u| ∧
      (|1 / 2 - u| = |1 / 2 - (0 : ℝ)| ↔ u = 0) := by
  have hu := (feasible_first_input_at_half u).mp ⟨v, hp⟩
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2 - 0),
    abs_of_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 / 2 - u)]
  constructor
  · linarith [hu.2]
  · constructor <;> intro h <;> linarith

theorem half_optimum_and_backup :
    terminalPlan (1 / 2) 0 (-1 / 2) ∧ terminalPlan (1 / 2) (-1 / 2) 0 := by
  norm_num [terminalPlan, X, U]

def replannedState (n : ℕ) : ℝ := if n = 0 then 1 else 1 / 2
def replannedInput (n : ℕ) : ℝ := if n = 0 then -1 / 2 else 0

theorem actual_replanned_trajectory (n : ℕ) :
    replannedState (n + 1) = replannedState n + replannedInput n ∧
      replannedState n ∈ X ∧ replannedInput n ∈ U := by
  by_cases hn : n = 0 <;> simp [replannedState, replannedInput, hn, X, U] <;> norm_num

theorem actual_replanned_first_input_optimal (n : ℕ) (u v : ℝ)
    (hp : terminalPlan (replannedState n) u v) :
    |1 / 2 - replannedInput n| ≤ |1 / 2 - u| := by
  by_cases hn : n = 0
  · simp only [replannedState, replannedInput, hn, if_pos] at hp ⊢
    rw [(unique_plan_at_one u v).mp hp |>.1]
  · simp only [replannedState, replannedInput, hn, if_neg] at hp ⊢
    exact (half_nearest_first_input u v hp).1

theorem safe_replanning_never_reaches_terminal (n : ℕ) : replannedState n ≠ 0 := by
  by_cases hn : n = 0 <;> simp [replannedState, hn]

def openPlan (drift x u v : ℝ) : Prop :=
  x ∈ X ∧ u ∈ U ∧ v ∈ U ∧ x + u + drift ∈ X ∧ x + u + drift + v + drift ∈ X

theorem zero_drift_X_control_invariant (x : ℝ) (hx : x ∈ X) :
    (0 : ℝ) ∈ U ∧ x + 0 ∈ X ∧ openPlan 0 x 0 0 := by
  exact ⟨by norm_num [U], by simpa using hx,
    ⟨hx, by norm_num [U], by norm_num [U], by simpa using hx, by simpa using hx⟩⟩

theorem zero_drift_half_RL_input : openPlan 0 (1 / 2) (1 / 2) 0 ∧
    (1 / 2 : ℝ) + 1 / 2 = 1 ∧ |1 / 2 - (1 / 2 : ℝ)| = 0 := by
  norm_num [openPlan, X, U]

theorem zero_drift_boundary_first_input (u : ℝ) :
    (∃ v, openPlan 0 1 u v) ↔ u ∈ Icc (-1 / 2) 0 := by
  constructor
  · rintro ⟨v, hp⟩
    exact ⟨hp.2.1.1, by linarith [hp.2.2.2.1.2]⟩
  · intro hu
    refine ⟨0, ?_⟩
    unfold openPlan X U
    exact ⟨by norm_num, ⟨hu.1, by linarith [hu.2]⟩, by norm_num,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩

theorem drift_first_input_exact (u : ℝ) :
    (∃ v, openPlan (3 / 5) (1 / 2) u v) ↔ u ∈ Icc (-1 / 2) (-1 / 5) := by
  constructor
  · rintro ⟨v, hp⟩
    exact ⟨hp.2.1.1, by linarith [hp.2.2.1.1, hp.2.2.2.2.2]⟩
  · intro hu
    refine ⟨-1 / 2, ?_⟩
    unfold openPlan X U
    exact ⟨by norm_num, ⟨hu.1, by linarith [hu.2]⟩, by norm_num,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩

theorem drift_nearest_first_input (u v : ℝ) (hp : openPlan (3 / 5) (1 / 2) u v) :
    |1 / 2 - (-1 / 5 : ℝ)| ≤ |1 / 2 - u| ∧
      (|1 / 2 - u| = |1 / 2 - (-1 / 5 : ℝ)| ↔ u = -1 / 5) := by
  have hu := (drift_first_input_exact u).mp ⟨v, hp⟩
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2 - (-1 / 5)),
    abs_of_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 / 2 - u)]
  constructor
  · linarith [hu.2]
  · constructor <;> intro h <;> linarith

theorem drift_actual_plan :
    openPlan (3 / 5) (1 / 2) (-1 / 5) (-1 / 2) ∧
      (1 / 2 : ℝ) - 1 / 5 + 3 / 5 = 9 / 10 ∧
        (9 / 10 : ℝ) - 1 / 2 + 3 / 5 = 1 := by
  norm_num [openPlan, X, U]

theorem drift_replanning_infeasible : ¬ ∃ u v, openPlan (3 / 5) (9 / 10) u v := by
  rintro ⟨u, v, hp⟩
  linarith [hp.2.1.1, hp.2.2.1.1, hp.2.2.2.2.2]

theorem drift_boundary_every_input_fails (u : ℝ) (hu : u ∈ U) :
    11 / 10 ≤ 1 + u + 3 / 5 ∧ 1 + u + 3 / 5 ∉ X := by
  constructor
  · linarith [hu.1]
  · intro hx
    linarith [hu.1, hx.2]

theorem every_drift_trajectory_grows (state input : ℕ → ℝ)
    (hu : ∀ n, input n ∈ U)
    (hstep : ∀ n, state (n + 1) = state n + input n + 3 / 5) (n : ℕ) :
    state 0 + n / 10 ≤ state n := by
  induction n with
  | zero => simp
  | succ n ih => rw [hstep]; push_cast; linarith [(hu n).1]

theorem no_all_time_safe_drift_trajectory (state input : ℕ → ℝ)
    (h0 : state 0 ∈ X) (hu : ∀ n, input n ∈ U)
    (hstep : ∀ n, state (n + 1) = state n + input n + 3 / 5) :
    state 21 ∉ X := by
  have hg := every_drift_trajectory_grows state input hu hstep 21
  intro hx
  norm_num at hg
  linarith [h0.1, hx.2]

theorem first_order_CBF_step (h alpha dt next : ℝ) (hh : 0 ≤ h) (hdt : 0 < dt)
    (hbound : alpha ≤ h / dt) (heuler : h - alpha * dt ≤ next) : 0 ≤ next := by
  have ha : alpha * dt ≤ h := (le_div_iff₀ hdt).mp hbound
  linarith

theorem strict_first_order_CBF_step (h alpha dt next : ℝ) (hh : 0 < h) (hdt : 0 < dt)
    (hbound : alpha < h / dt) (heuler : h - alpha * dt ≤ next) : 0 < next := by
  have ha : alpha * dt < h := (lt_div_iff₀ hdt).mp hbound
  linarith

end SafeLearning.CompletePredictiveSafety
