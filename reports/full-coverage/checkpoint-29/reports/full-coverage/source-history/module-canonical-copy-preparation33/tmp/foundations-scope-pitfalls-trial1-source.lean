import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsScopePitfalls

theorem actual_initial_safety_and_safe_successor_prove_all_time_safety
    {X : Type*} (F : X → X) (safe : Set X) (initial : X)
    (hinitial : initial ∈ safe) (hstep : ∀ x ∈ safe, F x ∈ safe) :
    ∀ t : ℕ, F^[t] initial ∈ safe := by
  intro t
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih

theorem actual_path_induction_uses_only_the_actual_step_obligation
    {X : Type*} (path : ℕ → X) (safe : Set X)
    (hinitial : path 0 ∈ safe)
    (hstep : ∀ t : ℕ, path t ∈ safe → path (t + 1) ∈ safe) :
    ∀ t : ℕ, path t ∈ safe := by
  intro t
  induction t with
  | zero => exact hinitial
  | succ t ih => exact hstep t ih

theorem actual_one_safe_simulation_does_not_imply_all_initial_states_are_safe :
    (∀ t : ℕ, (id : Bool → Bool)^[t] false = false) ∧
      ¬ (∀ initial : Bool, ∀ t : ℕ, (id : Bool → Bool)^[t] initial = false) := by
  constructor
  · intro t
    simp
  · intro h
    have hf := h true 0
    simpa using hf

theorem actual_conditioning_on_the_desired_invariance_does_not_prove_it :
    ((∀ t : ℕ, (fun _ : Bool => true)^[t] false = false) →
      ∀ t : ℕ, (fun _ : Bool => true)^[t] false = false) ∧
      ((fun _ : Bool => true)^[0] false = false) ∧
      ¬ (∀ t : ℕ, (fun _ : Bool => true)^[t] false = false) := by
  refine ⟨fun h => h, rfl, ?_⟩
  intro h
  have hf := h 1
  simpa using hf

def localSectorFunction (x : ℝ) : ℝ := if |x| ≤ 1 then 0 else 2 * x

theorem actual_sector_bound_on_its_box_holds_for_every_box_point :
    ∀ x ∈ Icc (-1 : ℝ) 1,
      (localSectorFunction x - 0 * x) * (localSectorFunction x - 1 * x) ≤ 0 := by
  intro x hx
  have habs : |x| ≤ 1 := abs_le.mpr hx
  simp [localSectorFunction, habs]

theorem actual_that_box_sector_bound_fails_outside_its_domain :
    (2 : ℝ) ∉ Icc (-1 : ℝ) 1 ∧
      localSectorFunction 2 = 4 ∧
      ¬ ((localSectorFunction 2 - 0 * 2) * (localSectorFunction 2 - 1 * 2) ≤ 0) := by
  norm_num [localSectorFunction]

theorem actual_multiplication_without_a_sign_premise_can_reverse_the_claim :
    (1 : ℝ) ≤ 2 ∧
      ¬ ((-1 : ℝ) * 1 ≤ (-1 : ℝ) * 2) ∧
      (-1 : ℝ) * 2 < (-1 : ℝ) * 1 := by
  norm_num

end SafeLearning.CompleteFoundationsScopePitfalls
