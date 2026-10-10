import SafeLearning.CompletePredictiveSafety

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompletePredictiveSafetyConsequences

open CompletePredictiveSafety

theorem zero_drift_boundary_nearest_input (u v : ℝ) (hp : openPlan 0 1 u v) :
    openPlan 0 1 0 0 ∧ |1 / 2 - (0 : ℝ)| ≤ |1 / 2 - u| ∧
      (|1 / 2 - u| = |1 / 2 - (0 : ℝ)| ↔ u = 0) := by
  have hu := (zero_drift_boundary_first_input u).mp ⟨v, hp⟩
  refine ⟨by norm_num [openPlan, X, U], ?_⟩
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2 - 0),
    abs_of_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 / 2 - u)]
  constructor
  · linarith [hu.2]
  · constructor <;> intro h <;> linarith

theorem actual_zero_drift_boundary_all_time (n : ℕ) :
    (1 : ℝ) ∈ X ∧ (0 : ℝ) ∈ U ∧ (1 : ℝ) + 0 = 1 ∧ openPlan 0 1 0 0 := by
  norm_num [X, U, openPlan]

def driftInvariant (S : Set ℝ) : Prop := ∀ x ∈ S, ∃ u ∈ U, x + u + 3 / 5 ∈ S

theorem empty_set_vacuously_control_invariant :
    (∅ : Set ℝ) ⊆ X ∧ driftInvariant ∅ := by
  simp [driftInvariant]

theorem no_nonempty_control_invariant_subset (S : Set ℝ) (hSX : S ⊆ X)
    (hne : S.Nonempty) : ¬ driftInvariant S := by
  classical
  intro hS
  obtain ⟨x0, hx0⟩ := hne
  let action (x : ℝ) : ℝ := if hx : x ∈ S then Classical.choose (hS x hx) else 0
  let step (x : ℝ) : ℝ := x + action x + 3 / 5
  let state (n : ℕ) : ℝ := step^[n] x0
  have haction (x : ℝ) (hx : x ∈ S) : action x ∈ U ∧ step x ∈ S := by
    simpa only [action, step, dif_pos hx] using Classical.choose_spec (hS x hx)
  have hmem (n : ℕ) : state n ∈ S := by
    induction n with
    | zero => exact hx0
    | succ n ih =>
      change step^[n + 1] x0 ∈ S
      rw [Function.iterate_succ_apply']
      exact (haction _ ih).2
  have hu (n : ℕ) : action (state n) ∈ U := (haction _ (hmem n)).1
  have hs (n : ℕ) : state (n + 1) = state n + action (state n) + 3 / 5 := by
    exact Function.iterate_succ_apply' step n x0
  have hf := no_all_time_safe_drift_trajectory state (fun n => action (state n))
    (hSX hx0) hu hs
  exact hf (hSX (hmem 21))

theorem held_quadratic_barrier_exact_counterexample :
    HasDerivAt (fun t : ℝ => t) 1 0 ∧
      HasDerivAt (fun t : ℝ => 1 - t ^ 2) 0 0 ∧
      (0 : ℝ) ≥ -(1 / 2) * (1 - (0 : ℝ) ^ 2) ∧
      (1 / 2 : ℝ) < (1 - (0 : ℝ) ^ 2) / (3 / 2) ∧
      (1 - (3 / 2 : ℝ) ^ 2) < 0 := by
  refine ⟨hasDerivAt_id 0, ?_, by norm_num, by norm_num, by norm_num⟩
  convert (hasDerivAt_const 0 (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).pow 2) using 1 <;>
    first | (ext t; simp [id_eq, Pi.sub_apply, Pi.pow_apply]) | norm_num [id_eq]

theorem exact_error_budget_step (h alpha dt error next : ℝ)
    (hmodel : h - alpha * dt - error ≤ next) (hbudget : alpha * dt + error ≤ h) :
    0 ≤ next := by linarith

theorem exact_strict_error_budget_step (h alpha dt error next : ℝ)
    (hmodel : h - alpha * dt - error ≤ next) (hbudget : alpha * dt + error < h) :
    0 < next := by linarith

theorem first_order_recursive_feasibility {State Action : Type*}
    (margin : State → ℝ) (next : State → Action → State) (admissible : Set Action)
    (alpha : ℝ → ℝ) (dt : ℝ) (hdt : 0 < dt)
    (hfeasible : ∀ x, 0 ≤ margin x → ∃ u ∈ admissible,
      margin x - alpha (margin x) * dt ≤ margin (next x u))
    (hstep : ∀ r : ℝ, 0 ≤ r → alpha r ≤ r / dt) (x : State) (hx : 0 ≤ margin x) :
    ∃ u ∈ admissible, 0 ≤ margin (next x u) ∧
      ∃ v ∈ admissible, margin (next x u) - alpha (margin (next x u)) * dt ≤
        margin (next (next x u) v) := by
  obtain ⟨u, hu, hmodel⟩ := hfeasible x hx
  have hsafe := first_order_CBF_step (margin x) (alpha (margin x)) dt
    (margin (next x u)) hx hdt (hstep _ hx) hmodel
  exact ⟨u, hu, hsafe, hfeasible (next x u) hsafe⟩

end SafeLearning.CompletePredictiveSafetyConsequences
