import SafeLearning.CompleteLyapunovTrajectoryValidation
import SafeLearning.CompleteModulesLandscapeLyapunovStability

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open CompleteLyapunovTrajectoryValidation

/-- This is the actual hybrid feedback: the approximation is used outside the
terminal set and the certified terminal controller inside it. -/
def switchedFeedback {S A : Type*} (terminal : Set S)
    (approx terminalControl : S → A) (state : S) : A := by
  classical
  exact if state ∈ terminal then terminalControl state else approx state

theorem actual_switched_feedback_agrees_with_the_approximation_before_entry
    {S A : Type*} (terminal : Set S) (approx terminalControl : S → A)
    (state : S) (hs : state ∉ terminal) :
    switchedFeedback terminal approx terminalControl state = approx state := by
  simp [switchedFeedback, hs]

theorem actual_switched_feedback_agrees_with_terminal_control_after_entry
    {S A : Type*} (terminal : Set S) (approx terminalControl : S → A)
    (state : S) (hs : state ∈ terminal) :
    switchedFeedback terminal approx terminalControl state = terminalControl state := by
  simp [switchedFeedback, hs]

theorem actual_switched_trajectory_matches_the_approximate_trajectory_through_first_entry
    {S A : Type*} (f : S × A → S) (approx terminalControl : S → A)
    (terminal : Set S) (initial : S) (entry : ℕ)
    (hfirst : ∀ t < entry, trajectory f approx t initial ∉ terminal) :
    ∀ t ≤ entry,
      trajectory f (switchedFeedback terminal approx terminalControl) t initial =
        trajectory f approx t initial := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      have hte : t < entry := by omega
      have heq := ih (by omega)
      simp only [trajectory, heq]
      rw [actual_switched_feedback_agrees_with_the_approximation_before_entry
        terminal approx terminalControl _ (hfirst t hte)]

theorem actual_terminal_controller_keeps_every_terminal_trajectory_in_the_terminal_set
    {S A : Type*} (f : S × A → S) (terminalControl : S → A)
    (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (initial : S) (hinitial : initial ∈ terminal) :
    ∀ t, trajectory f terminalControl t initial ∈ terminal := by
  intro t
  induction t with
  | zero => exact hinitial
  | succ t ih => exact hpreserve _ ih

theorem actual_switched_trajectory_inside_the_terminal_set_is_the_terminal_trajectory
    {S A : Type*} (f : S × A → S) (approx terminalControl : S → A)
    (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (initial : S) (hinitial : initial ∈ terminal) :
    ∀ t, trajectory f (switchedFeedback terminal approx terminalControl) t initial =
      trajectory f terminalControl t initial := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [trajectory, ih]
      rw [actual_switched_feedback_agrees_with_terminal_control_after_entry
        terminal approx terminalControl _
        (actual_terminal_controller_keeps_every_terminal_trajectory_in_the_terminal_set
          f terminalControl terminal hpreserve initial hinitial t)]

theorem actual_policy_trajectory_has_the_exact_time_shift_identity
    {S A : Type*} (f : S × A → S) (policy : S → A)
    (initial : S) (entry time : ℕ) :
    trajectory f policy (entry + time) initial =
      trajectory f policy time (trajectory f policy entry initial) := by
  induction time with
  | zero => simp [trajectory]
  | succ time ih => simp only [Nat.add_succ, trajectory, ih]

theorem actual_finite_entry_switched_trajectory_has_the_certified_terminal_suffix
    {S A : Type*} (f : S × A → S) (approx terminalControl : S → A)
    (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (initial : S) (entry : ℕ)
    (hfirst : ∀ t < entry, trajectory f approx t initial ∉ terminal)
    (hentry : trajectory f approx entry initial ∈ terminal) :
    ∀ time, trajectory f (switchedFeedback terminal approx terminalControl)
      (entry + time) initial =
        trajectory f terminalControl time (trajectory f approx entry initial) := by
  intro time
  rw [actual_policy_trajectory_has_the_exact_time_shift_identity]
  rw [actual_switched_trajectory_matches_the_approximate_trajectory_through_first_entry
    f approx terminalControl terminal initial entry hfirst entry le_rfl]
  exact actual_switched_trajectory_inside_the_terminal_set_is_the_terminal_trajectory
    f approx terminalControl terminal hpreserve _ hentry time

end SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
