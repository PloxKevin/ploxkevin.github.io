import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTerminalPlanShift

def terminalFeedback (state : ℝ) : ℝ := -state

theorem actual_terminal_feedback_is_feasible_and_preserves_the_terminal_set
    (state : ℝ) (hstate : |state|≤(1/2:ℝ)) :
    |state|≤2 ∧ |terminalFeedback state|≤1 ∧
    state+terminalFeedback state=0 ∧ |state+terminalFeedback state|≤(1/2:ℝ) := by
  simp only [terminalFeedback,abs_neg,add_neg_cancel,abs_zero]
  constructor
  · linarith
  constructor
  · linarith
  norm_num

structure FeasiblePlan (N : ℕ) (initial : ℝ) where
  state : ℕ→ℝ
  input : ℕ→ℝ
  initial_eq : state 0=initial
  recurrence : ∀ t : ℕ,t<N→state (t+1)=state t+input t
  state_bound : ∀ t : ℕ,t≤N→|state t|≤2
  input_bound : ∀ t : ℕ,t<N→|input t|≤1
  terminal_bound : |state N|≤(1/2:ℝ)

def shiftedState {N : ℕ} {initial : ℝ} (plan : FeasiblePlan N initial) (t : ℕ) : ℝ :=
  if t<N then plan.state (t+1) else 0

def shiftedInput {N : ℕ} {initial : ℝ} (plan : FeasiblePlan N initial) (t : ℕ) : ℝ :=
  if t+1<N then plan.input (t+1) else terminalFeedback (plan.state N)

theorem actual_executed_first_input_gives_the_old_predicted_next_state
    {N : ℕ} {initial : ℝ} (plan : FeasiblePlan N initial) (hN : 0<N) :
    initial+plan.input 0=plan.state 1 := by
  have h := plan.recurrence 0 hN
  simpa [plan.initial_eq] using h.symm

theorem actual_shifted_plan_initial_and_recurrence
    {N : ℕ} {initial : ℝ} (plan : FeasiblePlan N initial) (hN : 0<N) :
    shiftedState plan 0=initial+plan.input 0 ∧
    ∀t : ℕ,t<N→shiftedState plan (t+1)=shiftedState plan t+shiftedInput plan t := by
  constructor
  · rw [shiftedState,if_pos hN]
    exact (actual_executed_first_input_gives_the_old_predicted_next_state plan hN).symm
  · intro t ht
    by_cases hnext : t+1<N
    · rw [shiftedState,if_pos hnext,shiftedState,if_pos ht,shiftedInput,if_pos hnext]
      exact plan.recurrence (t+1) hnext
    · have hlast : t+1=N := by omega
      rw [shiftedState,if_neg hnext,shiftedState,if_pos ht,
        shiftedInput,if_neg hnext,hlast]
      simp [terminalFeedback]

theorem actual_shifted_plan_state_input_and_terminal_constraints
    {N : ℕ} {initial : ℝ} (plan : FeasiblePlan N initial) :
    (∀t : ℕ,t≤N→|shiftedState plan t|≤2) ∧
    (∀t : ℕ,t<N→|shiftedInput plan t|≤1) ∧ shiftedState plan N=0 ∧
    |shiftedState plan N|≤(1/2:ℝ) := by
  constructor
  · intro t ht
    by_cases h : t<N
    · rw [shiftedState,if_pos h]
      exact plan.state_bound (t+1) (by omega)
    · simp [shiftedState,h]
  constructor
  · intro t ht
    by_cases h : t+1<N
    · rw [shiftedInput,if_pos h]
      exact plan.input_bound (t+1) h
    · rw [shiftedInput,if_neg h]
      exact (actual_terminal_feedback_is_feasible_and_preserves_the_terminal_set
        (plan.state N) plan.terminal_bound).2.1
  simp [shiftedState]

def actualShiftedFeasiblePlan {N : ℕ} {initial : ℝ}
    (plan : FeasiblePlan N initial) (hN : 0<N) :
    FeasiblePlan N (initial+plan.input 0) where
  state := shiftedState plan
  input := shiftedInput plan
  initial_eq := (actual_shifted_plan_initial_and_recurrence plan hN).1
  recurrence := (actual_shifted_plan_initial_and_recurrence plan hN).2
  state_bound := (actual_shifted_plan_state_input_and_terminal_constraints plan).1
  input_bound := (actual_shifted_plan_state_input_and_terminal_constraints plan).2.1
  terminal_bound := (actual_shifted_plan_state_input_and_terminal_constraints plan).2.2.2

theorem actual_every_feasible_positive_horizon_plan_supplies_a_feasible_next_candidate
    (N : ℕ) (initial : ℝ) (hN : 0<N) (plan : FeasiblePlan N initial) :
    ∃next : FeasiblePlan N (initial+plan.input 0),
      (∀t : ℕ,t+1<N→next.input t=plan.input (t+1)) ∧
      next.input (N-1)=terminalFeedback (plan.state N) ∧ next.state N=0 := by
  refine ⟨actualShiftedFeasiblePlan plan hN,?_,?_,?_⟩
  · intro t ht
    exact if_pos ht
  · change shiftedInput plan (N-1)=_
    simp [shiftedInput,show N-1+1=N by omega]
  · exact (actual_shifted_plan_state_input_and_terminal_constraints plan).2.2.1

end SafeLearning.CompleteAppliedTerminalPlanShift
