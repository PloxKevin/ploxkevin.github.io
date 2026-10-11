import SafeLearning.CompleteCoreMPCFirstSuccessor27

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteCoreMPCTypedDomainShift28

/-- A precise reading of the primary Assumption1 with its displayed partial
domain. The successor-domain witness is part of the local contraction clause.
It does not supply a shifted plan, tightened constraint, or recursive
feasibility conclusion. Its correspondence to the primary needs independent
semantic review before this predicate can be used for source coverage. -/
structure TypedLocalIncrementalCertificate {S A : Type*}
    [NormedAddCommGroup S] [NormedAddCommGroup A]
    (X : Set S) (U : Set A) (f : S → A → S)
    (tracking : S → S → A → A) (V : S → S → A → ℝ)
    (cL delta k rho : ℝ) : Prop where
  cL_pos : 0 < cL
  delta_pos : 0 < delta
  k_nonneg : 0 ≤ k
  rho_nonneg : 0 ≤ rho
  rho_lt_one : rho < 1
  lower : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    V x z v ≤ delta → cL * ‖x-z‖ ^ 2 ≤ V x z v
  feedback : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    V x z v ≤ delta → ‖tracking x z v-v‖ ≤ k * ‖x-z‖
  successor_domain_and_contraction : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    ∀ vnext ∈ U, f z v ∈ X → V x z v ≤ delta →
      f x (tracking x z v) ∈ X ∧
      V (f x (tracking x z v)) (f z v) vnext ≤ rho * V x z v

def generatedTrackingState {S A : Type*}
    (f : S → A → S) (tracking : S → S → A → A)
    (nominal : ℕ → S) (reference : ℕ → A) (initial : S) : ℕ → S
  | 0 => initial
  | j+1 => f (generatedTrackingState f tracking nominal reference initial j)
      (tracking (generatedTrackingState f tracking nominal reference initial j)
        (nominal j) (reference j))

/-- The actual tracking recursion remains in the original state domain before
the lower bound is invoked. Only a local one-step certificate is supplied;
the all-stage conclusion follows by induction. -/
theorem actual_generated_tracking_states_have_original_domains_and_geometric_values
    {S A : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    (X : Set S) (U : Set A) (f : S → A → S)
    (tracking : S → S → A → A) (V : S → S → A → ℝ)
    (cL delta k rho B : ℝ)
    (certificate : TypedLocalIncrementalCertificate X U f tracking V cL delta k rho)
    (N : ℕ) (nominal : ℕ → S) (reference : ℕ → A) (initial : S)
    (hB0 : 0 ≤ B) (hB : B ≤ delta)
    (hnominal : ∀ j ≤ N, nominal j ∈ X)
    (hreference : ∀ j ≤ N, reference j ∈ U)
    (hdynamics : ∀ j < N, nominal (j+1) = f (nominal j) (reference j))
    (hinitial : initial ∈ X) (hvalue : V initial (nominal 0) (reference 0) ≤ B) :
    ∀ j ≤ N,
      generatedTrackingState f tracking nominal reference initial j ∈ X ∧
      V (generatedTrackingState f tracking nominal reference initial j)
        (nominal j) (reference j) ≤ rho ^ j * B := by
  intro j
  induction j with
  | zero =>
      intro _
      exact ⟨hinitial, by simpa [generatedTrackingState] using hvalue⟩
  | succ j ih =>
      intro hj
      have hjN : j < N := by omega
      have hprev := ih (by omega)
      have hpow : rho ^ j ≤ 1 :=
        pow_le_one₀ certificate.rho_nonneg certificate.rho_lt_one.le
      have hlocal : V (generatedTrackingState f tracking nominal reference initial j)
          (nominal j) (reference j) ≤ delta :=
        hprev.2.trans ((mul_le_mul_of_nonneg_right hpow hB0).trans (by simpa using hB))
      have hnext := certificate.successor_domain_and_contraction
        _ hprev.1 _ (hnominal j (by omega)) _ (hreference j (by omega))
        _ (hreference (j+1) hj) (by rw [← hdynamics j hjN]; exact hnominal (j+1) hj)
        hlocal
      constructor
      · simpa [generatedTrackingState] using hnext.1
      · calc
          V (generatedTrackingState f tracking nominal reference initial (j+1))
              (nominal (j+1)) (reference (j+1)) ≤
              rho * V (generatedTrackingState f tracking nominal reference initial j)
                (nominal j) (reference j) := by
                  simpa [generatedTrackingState, hdynamics j hjN] using hnext.2
          _ ≤ rho * (rho ^ j * B) :=
            mul_le_mul_of_nonneg_left hprev.2 certificate.rho_nonneg
          _ = rho ^ (j+1) * B := by rw [pow_succ]; ring

theorem actual_domain_valid_lower_bound_gives_the_true_tracking_radius
    {S : Type*} [NormedAddCommGroup S] (x z : S)
    (cL value radius : ℝ) (hcL : 0 < cL) (hradius : 0 ≤ radius)
    (hlower : cL * ‖x-z‖ ^ 2 ≤ value)
    (hupper : value ≤ cL * radius ^ 2) : ‖x-z‖ ≤ radius := by
  have hsquare : ‖x-z‖ ^ 2 ≤ radius ^ 2 :=
    (mul_le_mul_iff_right₀ hcL).mp (hlower.trans hupper)
  nlinarith [norm_nonneg (x-z)]

/-- A row is proved at its earlier tightened level from the later nominal
level and the actual tracking error. No membership of x in the new tightened
constraint is assumed. -/
theorem actual_tracking_radius_and_tightening_increment_give_the_state_row
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (row : S →L[ℝ] ℝ) (x z : S) (bound radius earlier later : ℝ)
    (hbound : ‖row‖ ≤ bound) (hbound0 : 0 ≤ bound)
    (hnominal : row z ≤ 1-later) (hradius : ‖x-z‖ ≤ radius)
    (hincrement : bound*radius ≤ later-earlier) : row x ≤ 1-earlier := by
  have herr : row (x-z) ≤ bound*radius := by
    calc
      row (x-z) ≤ ‖row (x-z)‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (row (x-z))
      _ ≤ ‖row‖ * ‖x-z‖ := row.le_opNorm (x-z)
      _ ≤ bound * ‖x-z‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ ≤ bound * radius := mul_le_mul_of_nonneg_left hradius hbound0
  rw [map_sub] at herr
  linarith

theorem actual_feedback_bound_and_tightening_increment_give_the_input_row
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (row : A →L[ℝ] ℝ) (actual nominal : A)
    (bound k radius earlier later : ℝ)
    (hbound : ‖row‖ ≤ bound) (hbound0 : 0 ≤ bound)
    (hnominal : row nominal ≤ 1-later)
    (hfeedback : ‖actual-nominal‖ ≤ k*radius)
    (hincrement : bound*(k*radius) ≤ later-earlier) : row actual ≤ 1-earlier := by
  exact actual_tracking_radius_and_tightening_increment_give_the_state_row
    row actual nominal bound (k*radius) earlier later hbound hbound0
    hnominal hfeedback hincrement

/-- The final tracking offset is the actual additive perturbation of the
terminal nominal successor. This instantiates robust terminal invariance
rather than assuming the new terminal state is feasible. -/
theorem actual_tracking_terminal_offset_is_absorbed_by_terminal_invariance
    {S A : Type*} [NormedAddCommGroup S]
    (f : S → A → S) (terminal : Set S) (terminalControl : S → A)
    (z actual : S) (radius : ℝ) (hz : z ∈ terminal)
    (hinvariant : ∀ z ∈ terminal, ∀ w : S, ‖w‖ ≤ radius →
      f z (terminalControl z)+w ∈ terminal)
    (hoffset : ‖actual-f z (terminalControl z)‖ ≤ radius) :
    actual ∈ terminal := by
  have h := hinvariant z hz (actual-f z (terminalControl z)) hoffset
  simpa using h

end SafeLearning.CompleteCoreMPCTypedDomainShift28


namespace SafeLearning.CompleteCoreMPCTypedDomainShift28

structure FiniteFeasiblePrediction {S A J K : Type*}
    [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    (f : S → A → S) (stateRows : J → S →L[ℝ] ℝ)
    (inputRows : K → A →L[ℝ] ℝ) (epsilon : ℕ → ℝ)
    (terminal : Set S) (N : ℕ) (initial : S) where
  state : ℕ → S
  input : ℕ → A
  initial_eq : state 0 = initial
  dynamics : ∀ j < N, state (j+1) = f (state j) (input j)
  state_constraints : ∀ j < N, ∀ row, stateRows row (state j) ≤ 1-epsilon j
  input_constraints : ∀ j < N, ∀ row, inputRows row (input j) ≤ 1-epsilon j
  terminal_constraint : state N ∈ terminal

/-- Every new state/input/terminal constraint is derived from the actual
tracking recursion. The nominal row premises concern the old shifted
reference plan; their construction from the original feasible prediction and
terminal ingredients is a separate explicit interface. Radius-budget premises
are scalar arithmetic to be instantiated by the source epsilon formula, not
new-state feasibility assumptions. -/
theorem actual_generated_tracking_candidate_constructs_a_feasible_new_prediction
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    (X : Set S) (U : Set A) (f : S → A → S)
    (tracking : S → S → A → A) (V : S → S → A → ℝ)
    (stateRows : J → S →L[ℝ] ℝ) (inputRows : K → A →L[ℝ] ℝ)
    (epsilon radius : ℕ → ℝ) (H L cL delta k rho B : ℝ)
    (certificate : TypedLocalIncrementalCertificate X U f tracking V cL delta k rho)
    (N : ℕ) (nominal : ℕ → S) (reference : ℕ → A) (initial : S)
    (hB0 : 0 ≤ B) (hB : B ≤ delta)
    (hnominal : ∀ j ≤ N, nominal j ∈ X)
    (hreference : ∀ j ≤ N, reference j ∈ U)
    (hdynamics : ∀ j < N, nominal (j+1) = f (nominal j) (reference j))
    (hinitial : initial ∈ X) (hvalue : V initial (nominal 0) (reference 0) ≤ B)
    (hradius0 : ∀ j ≤ N, 0 ≤ radius j)
    (hradiusbudget : ∀ j ≤ N, rho ^ j * B ≤ cL * radius j ^ 2)
    (hH0 : 0 ≤ H) (hL0 : 0 ≤ L)
    (hstateRows : ∀ row, ‖stateRows row‖ ≤ H)
    (hinputRows : ∀ row, ‖inputRows row‖ ≤ L)
    (hstateNominal : ∀ j < N, ∀ row,
      stateRows row (nominal j) ≤ 1-epsilon (j+1))
    (hinputNominal : ∀ j < N, ∀ row,
      inputRows row (reference j) ≤ 1-epsilon (j+1))
    (hstateIncrement : ∀ j < N, H*radius j ≤ epsilon (j+1)-epsilon j)
    (hinputIncrement : ∀ j < N, L*(k*radius j) ≤ epsilon (j+1)-epsilon j)
    (terminal : Set S) (terminalControl : S → A) (terminalPoint : S)
    (hterminalPoint : terminalPoint ∈ terminal)
    (hterminalNominal : nominal N = f terminalPoint (terminalControl terminalPoint))
    (hterminalInvariant : ∀ z ∈ terminal, ∀ w : S, ‖w‖ ≤ radius N →
      f z (terminalControl z)+w ∈ terminal) :
    Nonempty (FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial) := by
  let state := generatedTrackingState f tracking nominal reference initial
  let input := fun j => tracking (state j) (nominal j) (reference j)
  have htrack := actual_generated_tracking_states_have_original_domains_and_geometric_values
    X U f tracking V cL delta k rho B certificate N nominal reference initial
    hB0 hB hnominal hreference hdynamics hinitial hvalue
  have hlocal : ∀ j ≤ N, V (state j) (nominal j) (reference j) ≤ delta := by
    intro j hj
    have hpow : rho ^ j ≤ 1 :=
      pow_le_one₀ certificate.rho_nonneg certificate.rho_lt_one.le
    exact (htrack j hj).2.trans ((mul_le_mul_of_nonneg_right hpow hB0).trans (by simpa using hB))
  have herror : ∀ j ≤ N, ‖state j-nominal j‖ ≤ radius j := by
    intro j hj
    exact actual_domain_valid_lower_bound_gives_the_true_tracking_radius
      (state j) (nominal j) cL (V (state j) (nominal j) (reference j)) (radius j)
      certificate.cL_pos (hradius0 j hj)
      (certificate.lower _ (htrack j hj).1 _ (hnominal j hj)
        _ (hreference j hj) (hlocal j hj))
      ((htrack j hj).2.trans (hradiusbudget j hj))
  refine ⟨{
    state := state
    input := input
    initial_eq := rfl
    dynamics := ?_
    state_constraints := ?_
    input_constraints := ?_
    terminal_constraint := ?_
  }⟩
  · intro j _
    rfl
  · intro j hj row
    exact actual_tracking_radius_and_tightening_increment_give_the_state_row
      (stateRows row) (state j) (nominal j) H (radius j) (epsilon j) (epsilon (j+1))
      (hstateRows row) hH0 (hstateNominal j hj row) (herror j (by omega))
      (hstateIncrement j hj)
  · intro j hj row
    have hf := certificate.feedback _ (htrack j (by omega)).1
      _ (hnominal j (by omega)) _ (hreference j (by omega)) (hlocal j (by omega))
    have hb : ‖input j-reference j‖ ≤ k*radius j :=
      hf.trans (mul_le_mul_of_nonneg_left (herror j (by omega)) certificate.k_nonneg)
    exact actual_feedback_bound_and_tightening_increment_give_the_input_row
      (inputRows row) (input j) (reference j) L k (radius j) (epsilon j) (epsilon (j+1))
      (hinputRows row) hL0 (hinputNominal j hj row) hb (hinputIncrement j hj)
  · apply actual_tracking_terminal_offset_is_absorbed_by_terminal_invariance
      f terminal terminalControl terminalPoint (state N) (radius N)
      hterminalPoint hterminalInvariant
    simpa [hterminalNominal] using herror N (by omega)

end SafeLearning.CompleteCoreMPCTypedDomainShift28
