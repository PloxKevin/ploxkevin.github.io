import SafeLearning.CompleteFoundationsGraphViability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsFiniteHorizonViability
open SafeLearning.CompleteFoundationsFiniteSetIteration
open SafeLearning.CompleteFoundationsGraphViability

variable {State Input : Type*}

def finiteStates (F : State → Input → State) (initial : State) : List Input → List State
  | [] => [initial]
  | u::us => initial :: finiteStates F (F initial u) us

def safeControls (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) (initial : State) : List Input → Prop
  | [] => initial ∈ safe
  | u::us => initial ∈ safe ∧ allowed initial u ∧ safeControls F allowed safe (F initial u) us

theorem actual_finite_control_path_has_one_more_state_than_inputs
    (F : State → Input → State) (initial : State) (controls : List Input) :
    (finiteStates F initial controls).length = controls.length+1 := by
  induction controls generalizing initial with
  | nil => rfl
  | cons u us ih => simp [finiteStates,ih]

theorem actual_safe_control_path_starts_safe
    (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) (initial : State) (controls : List Input)
    (h : safeControls F allowed safe initial controls) : initial ∈ safe := by
  cases controls with
  | nil => exact h
  | cons u us => exact h.1

theorem actual_safe_control_path_has_every_constructed_state_safe
    (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) (initial : State) (controls : List Input)
    (h : safeControls F allowed safe initial controls) :
    ∀ x ∈ finiteStates F initial controls, x ∈ safe := by
  induction controls generalizing initial with
  | nil => simpa [finiteStates] using h
  | cons u us ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · exact hx ▸ h.1
    · exact ih (F initial u) h.2.2 x hx

theorem actual_safe_control_path_of_sufficient_length_survives_every_smaller_iterate
    (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) (n : ℕ) :
    ∀ initial controls, n ≤ controls.length →
      safeControls F allowed safe initial controls →
      initial ∈ iteration (viabilityStep F allowed) safe n := by
  induction n with
  | zero =>
    intro initial controls _ h
    exact actual_safe_control_path_starts_safe F allowed safe initial controls h
  | succ n ih =>
    intro initial controls hn h
    cases controls with
    | nil => simp at hn
    | cons u us =>
      have hn' : n ≤ us.length := by simpa using hn
      change initial ∈ iteration (viabilityStep F allowed) safe n ∧
        initial ∈ controlledPre F allowed (iteration (viabilityStep F allowed) safe n)
      exact ⟨ih initial (u::us) (by simp;omega) h,
        u,h.2.1,ih (F initial u) us hn' h.2.2⟩

theorem actual_every_shrinking_viability_iterate_constructs_an_admissible_safe_prefix
    (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) (n : ℕ) :
    ∀ initial, initial ∈ iteration (viabilityStep F allowed) safe n →
      ∃ controls : List Input, controls.length=n ∧
        safeControls F allowed safe initial controls := by
  induction n with
  | zero => intro initial h;exact ⟨[],rfl,h⟩
  | succ n ih =>
    intro initial h
    change initial ∈ iteration (viabilityStep F allowed) safe n ∧
      initial ∈ controlledPre F allowed (iteration (viabilityStep F allowed) safe n) at h
    obtain ⟨u,hu,hs⟩ := h.2
    obtain ⟨controls,hlen,hcontrols⟩ := ih (F initial u) hs
    have hi : initial ∈ safe :=
      actual_every_decreasing_iterate_is_contained_in_the_seed
        (viabilityStep F allowed) (actual_literal_shrinking_viability_step_is_monotone F allowed)
        safe (fun _ hx => hx.1) n h.1
    exact ⟨u::controls,by simp [hlen],hi,hu,hcontrols⟩

theorem actual_k_step_failure_avoidance_is_exactly_the_literal_shrinking_iteration
    (F : State → Input → State) (allowed : State → Input → Prop)
    (failed : Set State) (initial : State) (k : ℕ) :
    initial ∈ iteration (viabilityStep F allowed) (failedᶜ) k ↔
      ∃ controls : List Input, controls.length=k ∧
        safeControls F allowed (failedᶜ) initial controls := by
  constructor
  · exact actual_every_shrinking_viability_iterate_constructs_an_admissible_safe_prefix
      F allowed (failedᶜ) k initial
  · rintro ⟨controls,hlen,h⟩
    exact actual_safe_control_path_of_sufficient_length_survives_every_smaller_iterate
      F allowed (failedᶜ) k initial controls (by omega) h

end SafeLearning.CompleteFoundationsFiniteHorizonViability
