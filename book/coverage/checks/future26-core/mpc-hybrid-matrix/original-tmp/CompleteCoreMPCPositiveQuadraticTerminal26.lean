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
  | succ time ih => exact congrArg (fun state : S => f (state, policy state)) ih

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

namespace SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open CompleteLyapunovTrajectoryValidation

/-- A local robust certificate, whose derivation from a nonlinear MPC problem
remains a separate obligation. It quantifies over every admissible input error. -/
def robustOneStepCertificate {S A : Type*} [NormedAddCommGroup A]
    (f : S × A → S) (mpc : S → A) (feasible : Set S) (inputs : Set A)
    (eta : ℝ) : Prop :=
  ∀ state ∈ feasible, ∀ error : A, ‖error‖ ≤ eta →
    f (state, mpc state + error) ∈ feasible ∧ mpc state + error ∈ inputs

theorem actual_local_robust_certificate_applies_to_the_true_approximation_error
    {S A : Type*} [NormedAddCommGroup A] (f : S × A → S)
    (approx mpc : S → A) (feasible : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (state : S) (hstate : state ∈ feasible)
    (herror : ‖approx state - mpc state‖ ≤ eta) :
    f (state, approx state) ∈ feasible ∧ approx state ∈ inputs := by
  simpa only [add_sub_cancel] using hrobust state hstate (approx state - mpc state) herror

theorem actual_approximate_trajectory_is_feasible_through_the_checked_prefix
    {S A : Type*} [NormedAddCommGroup A] (f : S × A → S)
    (approx mpc : S → A) (feasible : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (initial : S) (hinitial : initial ∈ feasible) (entry : ℕ)
    (herror : ∀ t < entry, ‖approx (trajectory f approx t initial) -
      mpc (trajectory f approx t initial)‖ ≤ eta) :
    ∀ t ≤ entry, trajectory f approx t initial ∈ feasible := by
  intro t ht
  induction t with
  | zero => exact hinitial
  | succ t ih =>
      exact (actual_local_robust_certificate_applies_to_the_true_approximation_error
        f approx mpc feasible inputs eta hrobust _ (ih (by omega))
        (herror t (by omega))).1

theorem actual_approximate_inputs_obey_constraints_on_the_checked_prefix
    {S A : Type*} [NormedAddCommGroup A] (f : S × A → S)
    (approx mpc : S → A) (feasible : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (initial : S) (hinitial : initial ∈ feasible) (entry : ℕ)
    (herror : ∀ t < entry, ‖approx (trajectory f approx t initial) -
      mpc (trajectory f approx t initial)‖ ≤ eta) :
    ∀ t < entry, approx (trajectory f approx t initial) ∈ inputs := by
  intro t ht
  exact (actual_local_robust_certificate_applies_to_the_true_approximation_error
    f approx mpc feasible inputs eta hrobust _
    (actual_approximate_trajectory_is_feasible_through_the_checked_prefix
      f approx mpc feasible inputs eta hrobust initial hinitial entry herror t ht.le)
    (herror t ht)).2

theorem actual_good_finite_entry_initial_state_has_all_time_hybrid_state_and_input_safety
    {S A : Type*} [NormedAddCommGroup A] (f : S × A → S)
    (approx mpc terminalControl : S → A)
    (feasible terminal : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (hterminal : terminal ⊆ feasible)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (hinput : ∀ state ∈ terminal, terminalControl state ∈ inputs)
    (initial : S) (hinitial : initial ∈ feasible)
    (hgood : initial ∈ goodInitialStates f approx mpc terminal eta) :
    ∀ t, trajectory f (switchedFeedback terminal approx terminalControl) t initial ∈ feasible ∧
      switchedFeedback terminal approx terminalControl
        (trajectory f (switchedFeedback terminal approx terminalControl) t initial) ∈ inputs := by
  obtain ⟨entry, hentry, hchecked⟩ := hgood
  have hfirst := fun t ht => (hchecked t ht).1
  have herror := fun t ht => (hchecked t ht).2
  intro t
  by_cases ht : t < entry
  · rw [actual_switched_trajectory_matches_the_approximate_trajectory_through_first_entry
      f approx terminalControl terminal initial entry hfirst t ht.le]
    rw [actual_switched_feedback_agrees_with_the_approximation_before_entry
      terminal approx terminalControl _ (hfirst t ht)]
    exact ⟨actual_approximate_trajectory_is_feasible_through_the_checked_prefix
      f approx mpc feasible inputs eta hrobust initial hinitial entry herror t ht.le,
      actual_approximate_inputs_obey_constraints_on_the_checked_prefix
        f approx mpc feasible inputs eta hrobust initial hinitial entry herror t ht⟩
  · have htime : t = entry + (t - entry) := by omega
    rw [htime, actual_finite_entry_switched_trajectory_has_the_certified_terminal_suffix
      f approx terminalControl terminal hpreserve initial entry hfirst hentry]
    have hterm := actual_terminal_controller_keeps_every_terminal_trajectory_in_the_terminal_set
      f terminalControl terminal hpreserve _ hentry (t - entry)
    rw [actual_switched_feedback_agrees_with_terminal_control_after_entry
      terminal approx terminalControl _ hterm]
    exact ⟨hterminal hterm, hinput _ hterm⟩

theorem actual_policy_trajectory_equals_the_true_closed_loop_iterates
    {S A : Type*} (f : S × A → S) (policy : S → A) (initial : S) :
    ∀ t, trajectory f policy t initial = ((fun state => f (state, policy state))^[t]) initial := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      change f (trajectory f policy t initial, policy (trajectory f policy t initial)) = _
      rw [ih, Function.iterate_succ_apply']

theorem actual_finite_entry_hybrid_trajectory_converges_from_the_terminal_lyapunov_certificate
    {S A : Type*} [NormedAddCommGroup S] (f : S × A → S)
    (approx terminalControl : S → A) (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (V : S → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : Continuous (fun state => f (state, terminalControl state)))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hpositive : ∀ state, state ≠ 0 → 0 < V state)
    (hcompact : IsCompact {state : S | V state ≤ c})
    (hF0 : f (0, terminalControl 0) = 0)
    (hdecrease : ∀ state, V state ≤ c → state ≠ 0 →
      V (f (state, terminalControl state)) < V state)
    (hsublevel : ∀ state ∈ terminal, V state ≤ c)
    (initial : S) (entry : ℕ)
    (hfirst : ∀ t < entry, trajectory f approx t initial ∉ terminal)
    (hentry : trajectory f approx entry initial ∈ terminal) :
    Tendsto (fun t => trajectory f (switchedFeedback terminal approx terminalControl) t initial)
      atTop (𝓝 0) := by
  have hconverges :=
    (CompleteModulesLandscapeLyapunovStability.actual_positive_compact_strict_certificate_combines_stability_and_attraction
      (fun state => f (state, terminalControl state)) V c hc hF hV hV0
      hpositive hcompact hF0 hdecrease).2 _ (hsublevel _ hentry)
  apply (tendsto_add_atTop_iff_nat entry).1
  convert hconverges using 1
  ext t
  rw [Nat.add_comm t entry,
    actual_finite_entry_switched_trajectory_has_the_certified_terminal_suffix
      f approx terminalControl terminal hpreserve initial entry hfirst hentry,
    actual_policy_trajectory_equals_the_true_closed_loop_iterates]

end SafeLearning.CompleteCoreMPCFiniteEntrySwitch26

namespace SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open CompleteLyapunovTrajectoryValidation

def actualSafeConvergentInitialStates {S A : Type*} [NormedAddCommGroup S]
    (f : S × A → S) (approx terminalControl : S → A)
    (feasible terminal : Set S) (inputs : Set A) : Set S :=
  {initial | (∀ t, trajectory f (switchedFeedback terminal approx terminalControl) t initial ∈ feasible ∧
      switchedFeedback terminal approx terminalControl
        (trajectory f (switchedFeedback terminal approx terminalControl) t initial) ∈ inputs) ∧
    Tendsto (fun t => trajectory f (switchedFeedback terminal approx terminalControl) t initial)
      atTop (𝓝 0)}

theorem actual_checked_finite_entry_event_implies_the_safe_and_convergent_hybrid_outcome
    {S A : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    (f : S × A → S) (approx mpc terminalControl : S → A)
    (feasible terminal : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (hterminal : terminal ⊆ feasible)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (hinput : ∀ state ∈ terminal, terminalControl state ∈ inputs)
    (V : S → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : Continuous (fun state => f (state, terminalControl state)))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hpositive : ∀ state, state ≠ 0 → 0 < V state)
    (hcompact : IsCompact {state : S | V state ≤ c})
    (hF0 : f (0, terminalControl 0) = 0)
    (hdecrease : ∀ state, V state ≤ c → state ≠ 0 →
      V (f (state, terminalControl state)) < V state)
    (hsublevel : ∀ state ∈ terminal, V state ≤ c)
    (initial : S) (hinitial : initial ∈ feasible)
    (hgood : initial ∈ goodInitialStates f approx mpc terminal eta) :
    initial ∈ actualSafeConvergentInitialStates f approx terminalControl feasible terminal inputs := by
  refine ⟨actual_good_finite_entry_initial_state_has_all_time_hybrid_state_and_input_safety
    f approx mpc terminalControl feasible terminal inputs eta hrobust hterminal
    hpreserve hinput initial hinitial hgood, ?_⟩
  obtain ⟨entry, hentry, hchecked⟩ := hgood
  exact actual_finite_entry_hybrid_trajectory_converges_from_the_terminal_lyapunov_certificate
    f approx terminalControl terminal hpreserve V c hc hF hV hV0 hpositive
    hcompact hF0 hdecrease hsublevel initial entry (fun t ht => (hchecked t ht).1) hentry

theorem actual_initial_state_law_transfers_the_checked_event_probability_to_safe_convergence
    {S A : Type*} [NormedAddCommGroup S] [MeasurableSpace S] [NormedAddCommGroup A]
    (μ : Measure S) (f : S × A → S) (approx mpc terminalControl : S → A)
    (feasible terminal : Set S) (inputs : Set A) (eta : ℝ)
    (hrobust : robustOneStepCertificate f mpc feasible inputs eta)
    (hterminal : terminal ⊆ feasible)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (hinput : ∀ state ∈ terminal, terminalControl state ∈ inputs)
    (V : S → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : Continuous (fun state => f (state, terminalControl state)))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hpositive : ∀ state, state ≠ 0 → 0 < V state)
    (hcompact : IsCompact {state : S | V state ≤ c})
    (hF0 : f (0, terminalControl 0) = 0)
    (hdecrease : ∀ state, V state ≤ c → state ≠ 0 →
      V (f (state, terminalControl state)) < V state)
    (hsublevel : ∀ state ∈ terminal, V state ≤ c)
    (hfeasible : ∀ᵐ initial ∂μ, initial ∈ feasible) :
    μ (goodInitialStates f approx mpc terminal eta) ≤
      μ (actualSafeConvergentInitialStates f approx terminalControl feasible terminal inputs) := by
  apply measure_mono_ae
  filter_upwards [hfeasible] with initial hinitial
  intro hgood
  exact actual_checked_finite_entry_event_implies_the_safe_and_convergent_hybrid_outcome
    f approx mpc terminalControl feasible terminal inputs eta hrobust hterminal
    hpreserve hinput V c hc hF hV hV0 hpositive hcompact hF0 hdecrease hsublevel
    initial hinitial hgood

end SafeLearning.CompleteCoreMPCFiniteEntrySwitch26

namespace SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open CompleteLyapunovTrajectoryValidation

theorem actual_terminal_quadratic_dissipation_bounds_every_partial_state_energy
    {S : Type*} [NormedAddCommGroup S] (states : ℕ → S) (V : S → ℝ)
    (q : ℝ) (hdrop : ∀ t, V (states (t + 1)) ≤ V (states t) - q * ‖states t‖ ^ 2) :
    ∀ count : ℕ, q * (∑ t ∈ Finset.range count, ‖states t‖ ^ 2) +
      V (states count) ≤ V (states 0) := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Finset.sum_range_succ]
      nlinarith [hdrop count]

theorem actual_nonnegative_terminal_storage_and_strict_quadratic_dissipation_imply_convergence
    {S : Type*} [NormedAddCommGroup S] (states : ℕ → S) (V : S → ℝ)
    (q : ℝ) (hq : 0 < q) (hstorage : ∀ t, 0 ≤ V (states t))
    (hdrop : ∀ t, V (states (t + 1)) ≤ V (states t) - q * ‖states t‖ ^ 2) :
    Tendsto states atTop (𝓝 0) := by
  have hsum : Summable (fun t : ℕ => ‖states t‖ ^ 2) := by
    apply summable_of_sum_range_le (fun t => sq_nonneg _) (c := V (states 0) / q)
    intro count
    apply (le_div_iff₀ hq).2
    nlinarith [actual_terminal_quadratic_dissipation_bounds_every_partial_state_energy
      states V q hdrop count, hstorage count]
  have hz := hsum.tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.2
  convert Real.continuous_sqrt.continuousAt.tendsto.comp hz using 1
  · ext t
    exact (Real.sqrt_sq (norm_nonneg (states t))).symm
  · simp

theorem actual_terminal_invariance_and_quadratic_dissipation_prove_terminal_trajectory_convergence
    {S A : Type*} [NormedAddCommGroup S] (f : S × A → S)
    (terminalControl : S → A) (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (V : S → ℝ) (q : ℝ) (hq : 0 < q)
    (hstorage : ∀ state ∈ terminal, 0 ≤ V state)
    (hdrop : ∀ state ∈ terminal,
      V (f (state, terminalControl state)) ≤ V state - q * ‖state‖ ^ 2)
    (initial : S) (hinitial : initial ∈ terminal) :
    Tendsto (fun t => trajectory f terminalControl t initial) atTop (𝓝 0) := by
  have hterminal := actual_terminal_controller_keeps_every_terminal_trajectory_in_the_terminal_set
    f terminalControl terminal hpreserve initial hinitial
  apply actual_nonnegative_terminal_storage_and_strict_quadratic_dissipation_imply_convergence
    _ V q hq
  · intro t
    exact hstorage _ (hterminal t)
  · intro t
    exact hdrop _ (hterminal t)

end SafeLearning.CompleteCoreMPCFiniteEntrySwitch26

namespace SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open CompleteLyapunovTrajectoryValidation

theorem actual_positive_continuous_quadratic_form_has_a_uniform_strict_norm_bound
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [ProperSpace S] [Nontrivial S]
    (Q : S → ℝ) (hQ : Continuous Q) (hpositive : ∀ state, state ≠ 0 → 0 < Q state)
    (hscale : ∀ (factor : ℝ) state, Q (factor • state) = factor ^ 2 * Q state) :
    ∃ q : ℝ, 0 < q ∧ ∀ state, q * ‖state‖ ^ 2 ≤ Q state := by
  obtain ⟨unit, hunit⟩ := exists_norm_eq S (show (0 : ℝ) ≤ 1 by positivity)
  have hunitmem : unit ∈ Metric.sphere (0 : S) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit
  obtain ⟨smallest, hsmallest, hminimum⟩ :=
    (isCompact_sphere (0 : S) 1).exists_isMinOn ⟨unit, hunitmem⟩ hQ.continuousOn
  have hsmallestnorm : ‖smallest‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hsmallest
  have hsmallestne : smallest ≠ 0 := by
    intro hz
    simpa [hz] using hsmallestnorm
  refine ⟨Q smallest, hpositive smallest hsmallestne, ?_⟩
  intro state
  by_cases hz : state = 0
  · have hzero : Q (0 : S) = 0 := by simpa using hscale 0 (0 : S)
    simp [hz, hzero]
  · have hn : 0 < ‖state‖ := norm_pos_iff.mpr hz
    have hnormalized : ‖state‖⁻¹ • state ∈ Metric.sphere (0 : S) 1 := by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hmin := hminimum hnormalized
    have hrescale : Q state = ‖state‖ ^ 2 * Q (‖state‖⁻¹ • state) := by
      simpa only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using
        hscale ‖state‖ (‖state‖⁻¹ • state)
    rw [hrescale, mul_comm (Q smallest)]
    exact mul_le_mul_of_nonneg_left hmin (sq_nonneg ‖state‖)

theorem actual_positive_quadratic_terminal_cost_and_nonnegative_storage_prove_convergence
    {S A : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [ProperSpace S] [Nontrivial S]
    (f : S × A → S) (terminalControl : S → A) (terminal : Set S)
    (hpreserve : ∀ state ∈ terminal, f (state, terminalControl state) ∈ terminal)
    (V Q : S → ℝ) (R : A → ℝ)
    (hQ : Continuous Q) (hpositive : ∀ state, state ≠ 0 → 0 < Q state)
    (hscale : ∀ (factor : ℝ) state, Q (factor • state) = factor ^ 2 * Q state)
    (hstorage : ∀ state ∈ terminal, 0 ≤ V state)
    (hinputcost : ∀ state ∈ terminal, 0 ≤ R (terminalControl state))
    (hdrop : ∀ state ∈ terminal,
      V (f (state, terminalControl state)) ≤ V state - (Q state + R (terminalControl state)))
    (initial : S) (hinitial : initial ∈ terminal) :
    Tendsto (fun t => trajectory f terminalControl t initial) atTop (𝓝 0) := by
  obtain ⟨q, hq, hbound⟩ :=
    actual_positive_continuous_quadratic_form_has_a_uniform_strict_norm_bound Q hQ hpositive hscale
  apply actual_terminal_invariance_and_quadratic_dissipation_prove_terminal_trajectory_convergence
    f terminalControl terminal hpreserve V q hq hstorage
  · intro state hstate
    linarith [hbound state, hinputcost state hstate, hdrop state hstate]
  · exact hinitial

end SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
