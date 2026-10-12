import SafeLearning.CompleteCoreMPCHybridMatrixInfinityInput26
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Algebra.Field.GeomSum

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


namespace SafeLearning.CompleteCoreMPCTypedDomainShift28

def oldPlanExtendedState
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A) (j : ℕ) : S :=
  if j ≤ N then plan.state j else f (plan.state N) (terminalControl (plan.state N))

def oldPlanExtendedInput
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A) (j : ℕ) : A :=
  if j < N then plan.input j else terminalControl (oldPlanExtendedState plan terminalControl j)

/-- Extension by the actual terminal controller retains the actual plant
recurrence, including the last step. No feasible new prediction is assumed. -/
theorem actual_old_feasible_plan_extends_by_the_terminal_plant_step
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A) :
    ∀ j ≤ N, oldPlanExtendedState plan terminalControl (j+1) =
      f (oldPlanExtendedState plan terminalControl j)
        (oldPlanExtendedInput plan terminalControl j) := by
  intro j hj
  by_cases hjN : j < N
  · have hjnext : j+1 ≤ N := by omega
    simp only [oldPlanExtendedState, if_pos hj, if_pos hjnext,
      oldPlanExtendedInput, if_pos hjN]
    exact plan.dynamics j hjN
  · have heq : j = N := by omega
    subst j
    simp [oldPlanExtendedState, oldPlanExtendedInput]

/-- The later row bounds used in the tracking proof are derived from the old
feasible prediction and the terminal controller's original stage bounds. -/
theorem actual_old_shifted_reference_has_its_true_later_tightened_rows
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, stateRows row x ≤ 1-epsilon N) ∧
      (∀ row, inputRows row (terminalControl x) ≤ 1-epsilon N)) :
    ∀ j < N,
      (∀ row, stateRows row (oldPlanExtendedState plan terminalControl (j+1))
        ≤ 1-epsilon (j+1)) ∧
      (∀ row, inputRows row (oldPlanExtendedInput plan terminalControl (j+1))
        ≤ 1-epsilon (j+1)) := by
  intro j hj
  have hjnext : j+1 ≤ N := by omega
  by_cases hstrict : j+1 < N
  · constructor
    · intro row
      simpa only [oldPlanExtendedState, if_pos hjnext] using
        plan.state_constraints (j+1) hstrict row
    · intro row
      simpa only [oldPlanExtendedInput, if_pos hstrict] using
        plan.input_constraints (j+1) hstrict row
  · have heq : j+1 = N := by omega
    have hrows := hterminalRows (plan.state N) plan.terminal_constraint
    constructor
    · intro row
      simpa [heq, oldPlanExtendedState] using hrows.1 row
    · intro row
      simpa [heq, oldPlanExtendedState, oldPlanExtendedInput] using hrows.2 row

/-- The original-domain conditions for the shifted reference, including its
new terminal reference input, follow from old tightened rows, nonnegative
budgets and true terminal invariance. The domain X is the actual original
polytope and Ut is contained in the original input domain U. -/
theorem actual_old_reference_extension_stays_in_the_original_domains
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A) (X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRows row x ≤ 1)
    (hUt : ∀ u, (∀ row, inputRows row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j ≤ N, 0 ≤ epsilon j)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, stateRows row x ≤ 1-epsilon N) ∧
      (∀ row, inputRows row (terminalControl x) ≤ 1-epsilon N))
    (hinvariant : ∀ x ∈ terminal, f x (terminalControl x) ∈ terminal) :
    ∀ j ≤ N+1,
      oldPlanExtendedState plan terminalControl j ∈ X ∧
      oldPlanExtendedInput plan terminalControl j ∈ U := by
  have hterminalDomain : ∀ x ∈ terminal, x ∈ X ∧ terminalControl x ∈ U := by
    intro x hx
    have hr := hterminalRows x hx
    have he := hepsilon N (by omega)
    constructor
    · apply (hX x).2
      intro row
      exact (hr.1 row).trans (by linarith)
    · apply hUt
      intro row
      exact (hr.2 row).trans (by linarith)
  intro j hj
  by_cases hstrict : j < N
  · have hjN : j ≤ N := by omega
    have he := hepsilon j hjN
    constructor
    · apply (hX _).2
      intro row
      have hr := plan.state_constraints j hstrict row
      simpa only [oldPlanExtendedState, if_pos hjN] using hr.trans (by linarith)
    · apply hUt
      intro row
      have hr := plan.input_constraints j hstrict row
      simpa only [oldPlanExtendedInput, if_pos hstrict] using hr.trans (by linarith)
  · by_cases heq : j = N
    · subst j
      simpa [oldPlanExtendedState, oldPlanExtendedInput] using
        hterminalDomain (plan.state N) plan.terminal_constraint
    · have hjlarge : ¬ j ≤ N := by omega
      have hdomain := hterminalDomain
        (f (plan.state N) (terminalControl (plan.state N)))
        (hinvariant (plan.state N) plan.terminal_constraint)
      simpa only [oldPlanExtendedState, if_neg hjlarge,
        oldPlanExtendedInput, if_neg hstrict] using hdomain

/-- All finite-horizon reference assumptions used by the existing tracking
constructor are now supplied by the old feasible plan, not by a postulated
new feasible plan or assumed actual successor memberships. -/
theorem actual_old_feasible_plan_supplies_every_shifted_reference_assumption
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    {f : S → A → S} {stateRows : J → S →L[ℝ] ℝ}
    {inputRows : K → A →L[ℝ] ℝ} {epsilon : ℕ → ℝ}
    {terminal : Set S} {N : ℕ} {initial : S}
    (plan : FiniteFeasiblePrediction f stateRows inputRows epsilon terminal N initial)
    (terminalControl : S → A) (X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRows row x ≤ 1)
    (hUt : ∀ u, (∀ row, inputRows row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j ≤ N, 0 ≤ epsilon j)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, stateRows row x ≤ 1-epsilon N) ∧
      (∀ row, inputRows row (terminalControl x) ≤ 1-epsilon N))
    (hinvariant : ∀ x ∈ terminal, f x (terminalControl x) ∈ terminal) :
    let nominal := fun j => oldPlanExtendedState plan terminalControl (j+1)
    let reference := fun j => oldPlanExtendedInput plan terminalControl (j+1)
    (∀ j ≤ N, nominal j ∈ X) ∧
    (∀ j ≤ N, reference j ∈ U) ∧
    (∀ j < N, nominal (j+1) = f (nominal j) (reference j)) ∧
    (∀ j < N, ∀ row, stateRows row (nominal j) ≤ 1-epsilon (j+1)) ∧
    (∀ j < N, ∀ row, inputRows row (reference j) ≤ 1-epsilon (j+1)) ∧
    nominal N = f (plan.state N) (terminalControl (plan.state N)) := by
  dsimp
  have hdomains := actual_old_reference_extension_stays_in_the_original_domains
    plan terminalControl X U hX hUt hepsilon hterminalRows hinvariant
  have hrows := actual_old_shifted_reference_has_its_true_later_tightened_rows
    plan terminalControl hterminalRows
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (hdomains (j+1) (by omega)).1
  · intro j hj
    exact (hdomains (j+1) (by omega)).2
  · intro j hj
    simpa [Nat.add_assoc] using
      actual_old_feasible_plan_extends_by_the_terminal_plant_step
        plan terminalControl (j+1) (by omega)
  · intro j hj row
    exact (hrows j hj).1 row
  · intro j hj row
    exact (hrows j hj).2 row
  · simp [oldPlanExtendedState]

end SafeLearning.CompleteCoreMPCTypedDomainShift28

set_option autoImplicit false
noncomputable section
open Finset

namespace SafeLearning.CompleteCoreMPCExactTightening28

def originalTrackingRadius (rho cL cU lambda eta : ℝ) (j : ℕ) : ℝ :=
  (Real.sqrt rho) ^ j * (lambda * eta * Real.sqrt (cU / cL))

def originalTightening (epsilon rho : ℝ) (j : ℕ) : ℝ :=
  epsilon * ∑ i ∈ Finset.range j, (Real.sqrt rho) ^ i

/-- The source radius budget is an exact identity, not an upper bound supplied
as a premise. This includes zero input disturbance and singular row norms. -/
theorem actual_original_radius_has_the_exact_geometric_value_budget
    (rho cL cU lambda eta : ℝ) (j : ℕ)
    (hrho : 0 ≤ rho) (hcL : 0 < cL) (hcU : 0 ≤ cU)
    (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) :
    0 ≤ originalTrackingRadius rho cL cU lambda eta j ∧
    rho ^ j * (cU * (lambda * eta) ^ 2) =
      cL * originalTrackingRadius rho cL cU lambda eta j ^ 2 := by
  have hratio : 0 ≤ cU / cL := div_nonneg hcU hcL.le
  have hq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho
  have hp : ((Real.sqrt rho) ^ j) ^ 2 = rho ^ j := by
    calc
      ((Real.sqrt rho) ^ j) ^ 2 = ((Real.sqrt rho) ^ 2) ^ j := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = rho ^ j := by rw [hq]
  have hcancel : cL * (cU / cL) = cU := by
    field_simp
  constructor
  · exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg rho) j)
      (mul_nonneg (mul_nonneg hlambda heta) (Real.sqrt_nonneg _))
  · dsimp [originalTrackingRadius]
    simp only [mul_pow, hp, Real.sq_sqrt hratio]
    linear_combination -(rho ^ j * (lambda ^ 2 * eta ^ 2)) * hcancel

/-- Increasing the finite tightening by one stage adds exactly the current
geometric increment. Every budget is nonnegative and the levels are monotone. -/
theorem actual_original_tightening_has_exact_increments_and_is_monotone
    (epsilon rho : ℝ) (hepsilon : 0 ≤ epsilon) :
    (∀ j, 0 ≤ originalTightening epsilon rho j) ∧
    (∀ j, originalTightening epsilon rho (j+1)-originalTightening epsilon rho j =
      epsilon * (Real.sqrt rho) ^ j) ∧
    Monotone (originalTightening epsilon rho) := by
  have hnonneg : ∀ j, 0 ≤ originalTightening epsilon rho j := by
    intro j
    exact mul_nonneg hepsilon (Finset.sum_nonneg (fun i _ => pow_nonneg (Real.sqrt_nonneg rho) i))
  have hincrement : ∀ j,
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j =
        epsilon * (Real.sqrt rho) ^ j := by
    intro j
    simp only [originalTightening, Finset.sum_range_succ]
    ring
  refine ⟨hnonneg, hincrement, monotone_nat_of_le_succ ?_⟩
  intro j
  have h := hincrement j
  have hp := mul_nonneg hepsilon (pow_nonneg (Real.sqrt_nonneg rho) j)
  linarith

/-- The printed max of row norms bounds both actual state and input tracking
increments with the source's exact radius and tightening formula. -/
theorem actual_original_max_norm_tightening_covers_both_tracking_rows
    (rho cL cU lambda eta H L k : ℝ) (j : ℕ)
    (hcL : 0 < cL) (hcU : 0 ≤ cU) (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hk : 0 ≤ k) :
    let epsilon := lambda * eta * Real.sqrt (cU/cL) * max H (L*k)
    0 ≤ epsilon ∧
    H * originalTrackingRadius rho cL cU lambda eta j ≤
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j ∧
    L * (k * originalTrackingRadius rho cL cU lambda eta j) ≤
      originalTightening epsilon rho (j+1)-originalTightening epsilon rho j := by
  dsimp
  let R := lambda * eta * Real.sqrt (cU/cL)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg hlambda heta) (Real.sqrt_nonneg _)
  have hM : 0 ≤ max H (L*k) := hH.trans (le_max_left _ _)
  have hepsilon : 0 ≤ R * max H (L*k) := mul_nonneg hR hM
  have hinc := (actual_original_tightening_has_exact_increments_and_is_monotone
    (R * max H (L*k)) rho hepsilon).2.1 j
  have hq := pow_nonneg (Real.sqrt_nonneg rho) j
  have hstate := mul_le_mul_of_nonneg_left (le_max_left H (L*k)) (mul_nonneg hq hR)
  have hinput := mul_le_mul_of_nonneg_left (le_max_right H (L*k)) (mul_nonneg hq hR)
  refine ⟨hepsilon, ?_, ?_⟩
  · change H * ((Real.sqrt rho)^j * R) ≤ _
    rw [hinc]
    nlinarith [hstate]
  · change L * (k * ((Real.sqrt rho)^j * R)) ≤ _
    rw [hinc]
    nlinarith [hinput]

/-- The finite sum is exactly the displayed quotient when the contraction
rate is in its original interval. The denominator is strictly positive. -/
theorem actual_original_tightening_is_the_printed_geometric_quotient
    (epsilon rho : ℝ) (j : ℕ) (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    0 < 1-Real.sqrt rho ∧
    originalTightening epsilon rho j =
      epsilon * (1-(Real.sqrt rho)^j)/(1-Real.sqrt rho) := by
  have hq0 := Real.sqrt_nonneg rho
  have hq2 := Real.sq_sqrt hrho
  have hq1 : Real.sqrt rho < 1 := by nlinarith
  constructor
  · linarith
  · dsimp [originalTightening]
    rw [geom_sum_eq (ne_of_lt hq1)]
    apply (eq_div_iff (sub_ne_zero.mpr hq1.ne.symm)).2
    have hcancel : ((Real.sqrt rho ^ j-1)/(Real.sqrt rho-1)) *
        (1-Real.sqrt rho) = 1-Real.sqrt rho ^ j := by
      rw [show 1-Real.sqrt rho = -(Real.sqrt rho-1) by ring,
        mul_neg, div_mul_cancel₀ _ (sub_ne_zero.mpr hq1.ne)]
      ring
    calc
      epsilon * ((Real.sqrt rho ^ j-1)/(Real.sqrt rho-1)) * (1-Real.sqrt rho) =
          epsilon * (((Real.sqrt rho ^ j-1)/(Real.sqrt rho-1)) * (1-Real.sqrt rho)) := by ring
      _ = epsilon * (1-Real.sqrt rho ^ j) := by rw [hcancel]

end SafeLearning.CompleteCoreMPCExactTightening28


namespace SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCExactTightening28

/-- The actual old feasible prediction supplies the complete shifted
reference. The source epsilon/radius formulas supply every scalar row budget.
Only the separately derived first disturbed-successor bootstrap is exposed
here; no new feasible plan or new tightened row is assumed. -/
theorem actual_old_feasible_plan_and_source_budgets_construct_a_true_shifted_prediction
    {S A J K : Type*} [NormedAddCommGroup S] [NormedAddCommGroup A]
    [NormedSpace ℝ S] [NormedSpace ℝ A]
    (X : Set S) (U : Set A) (f : S → A → S)
    (tracking : S → S → A → A) (V : S → S → A → ℝ)
    (stateRows : J → S →L[ℝ] ℝ) (inputRows : K → A →L[ℝ] ℝ)
    (cL delta k rho cU lambda eta H L : ℝ)
    (certificate : TypedLocalIncrementalCertificate X U f tracking V cL delta k rho)
    (hcU : 0 ≤ cU) (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta)
    (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hsmall : cU*(lambda*eta)^2 ≤ delta)
    (hstateRows : ∀ row, ‖stateRows row‖ ≤ H)
    (hinputRows : ∀ row, ‖inputRows row‖ ≤ L)
    (terminal : Set S) (terminalControl : S → A) (N : ℕ) (initial next : S)
    (plan : FiniteFeasiblePrediction f stateRows inputRows
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max H (L*k)) rho)
      terminal N initial)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRows row x ≤ 1)
    (hUt : ∀ u, (∀ row, inputRows row u ≤ 1) → u ∈ U)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, stateRows row x ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max H (L*k)) rho N) ∧
      (∀ row, inputRows row (terminalControl x) ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max H (L*k)) rho N))
    (hterminalRobust : ∀ x ∈ terminal, ∀ w : S,
      ‖w‖ ≤ originalTrackingRadius rho cL cU lambda eta N →
      f x (terminalControl x)+w ∈ terminal)
    (hnextX : next ∈ X)
    (hnextV : V next (oldPlanExtendedState plan terminalControl 1)
      (oldPlanExtendedInput plan terminalControl 1) ≤ cU*(lambda*eta)^2) :
    Nonempty (FiniteFeasiblePrediction f stateRows inputRows
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max H (L*k)) rho)
      terminal N next) := by
  let epsilon := lambda*eta*Real.sqrt (cU/cL)*max H (L*k)
  have hincrements := fun j => actual_original_max_norm_tightening_covers_both_tracking_rows
    rho cL cU lambda eta H L k j certificate.cL_pos hcU hlambda heta hH hL
    certificate.k_nonneg
  have hepsilon : 0 ≤ epsilon := (hincrements 0).1
  have he : ∀ j ≤ N, 0 ≤ originalTightening epsilon rho j := by
    intro j _
    exact (actual_original_tightening_has_exact_increments_and_is_monotone
      epsilon rho hepsilon).1 j
  have hradius := fun j => actual_original_radius_has_the_exact_geometric_value_budget
    rho cL cU lambda eta j certificate.rho_nonneg certificate.cL_pos hcU hlambda heta
  have hterminalInvariant : ∀ x ∈ terminal, f x (terminalControl x) ∈ terminal := by
    intro x hx
    have h := hterminalRobust x hx 0 (by simpa using (hradius N).1)
    simpa using h
  have href := actual_old_feasible_plan_supplies_every_shifted_reference_assumption
    plan terminalControl X U hX hUt he hterminalRows hterminalInvariant
  dsimp at href
  exact actual_generated_tracking_candidate_constructs_a_feasible_new_prediction
    X U f tracking V stateRows inputRows (originalTightening epsilon rho)
    (originalTrackingRadius rho cL cU lambda eta) H L cL delta k rho
    (cU*(lambda*eta)^2) certificate N
    (fun j => oldPlanExtendedState plan terminalControl (j+1))
    (fun j => oldPlanExtendedInput plan terminalControl (j+1)) next
    (mul_nonneg hcU (sq_nonneg _)) hsmall href.1 href.2.1 href.2.2.1
    hnextX hnextV
    (fun j _ => (hradius j).1)
    (fun j _ => (hradius j).2.le)
    hH hL hstateRows hinputRows href.2.2.2.1 href.2.2.2.2.1
    (fun j _ => (hincrements j).2.1)
    (fun j _ => (hincrements j).2.2)
    terminal terminalControl (plan.state N) plan.terminal_constraint
    href.2.2.2.2.2 hterminalRobust

/-- The uncertainty radius used by the actual finite tracking proof is the
same real scalar as the source terminal-ball radius. No terminal membership
or constraint-satisfaction conclusion is hidden in this equality. -/
theorem actual_geometric_tracking_radius_is_the_printed_terminal_ball_radius
    (rho cL cU lambda eta : ℝ) (N : ℕ)
    (hrho : 0 ≤ rho) (hcL : 0 < cL) (hcU : 0 ≤ cU) :
    originalTrackingRadius rho cL cU lambda eta N =
      Real.sqrt (rho^N*cU/cL)*lambda*eta := by
  have hratio : 0 ≤ cU/cL := div_nonneg hcU hcL.le
  have hp : ((Real.sqrt rho)^N)^2=rho^N := by
    calc
      ((Real.sqrt rho)^N)^2=((Real.sqrt rho)^2)^N := by
        rw [← pow_mul,← pow_mul]
        congr 1
        omega
      _ = rho^N := by rw [Real.sq_sqrt hrho]
  have hs : ((Real.sqrt rho)^N*Real.sqrt (cU/cL))^2=rho^N*cU/cL := by
    rw [mul_pow,hp,Real.sq_sqrt hratio]
    ring
  have hroot := Real.sq_sqrt (show 0 ≤ rho^N*cU/cL by positivity)
  have hleft : 0 ≤ (Real.sqrt rho)^N*Real.sqrt (cU/cL) := by positivity
  have hright := Real.sqrt_nonneg (rho^N*cU/cL)
  have heq : (Real.sqrt rho)^N*Real.sqrt (cU/cL)=Real.sqrt (rho^N*cU/cL) := by
    nlinarith
  unfold originalTrackingRadius
  calc
    (Real.sqrt rho)^N*(lambda*eta*Real.sqrt (cU/cL)) =
        ((Real.sqrt rho)^N*Real.sqrt (cU/cL))*lambda*eta := by ring
    _ = Real.sqrt (rho^N*cU/cL)*lambda*eta := by rw [heq]

end SafeLearning.CompleteCoreMPCTypedDomainShift28


namespace SafeLearning.CompleteCoreMPCLocalGeometry28
open SafeLearning.CompleteCoreMPCNormBridge27
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- Actual linear rows with unit right-hand sides leave an explicit open ball
about zero in the state set. The zero-row case is covered by the same radius. -/
theorem actual_polytopic_state_set_contains_an_explicit_positive_origin_ball
    {I J : Type*} [Fintype I] [Fintype J] (H : Matrix J I ℝ) :
    0 < 1 / (‖H‖ + 1) ∧
    Metric.ball (0 : EuclideanSpace ℝ I) (1 / (‖H‖ + 1)) ⊆
      {x | ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1} := by
  have hdenom : 0 < ‖H‖ + 1 := by linarith [norm_nonneg H]
  have hr : 0 < 1 / (‖H‖ + 1) := div_pos zero_lt_one hdenom
  refine ⟨hr, ?_⟩
  intro x hx j
  have hxnorm : ‖x‖ < 1 / (‖H‖ + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hrow := actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H x j
  have hproduct : ‖H‖ * (1 / (‖H‖ + 1)) < 1 := by
    rw [mul_one_div]
    exact (div_lt_one hdenom).2 (by linarith)
  calc
    (H *ᵥ (fun i => x i)) j ≤ |(H *ᵥ (fun i => x i)) j| := le_abs_self _
    _ ≤ ‖H‖ * ‖x‖ := hrow
    _ ≤ ‖H‖ * (1 / (‖H‖ + 1)) :=
      mul_le_mul_of_nonneg_left hxnorm.le (norm_nonneg H)
    _ ≤ 1 := hproduct.le

/-- Continuity and a genuine positive-radius state neighbourhood give an
actual distinct local pair. Constants are ordered from the local inequalities,
rather than by asserting their order as an extra premise. The nontrivial state
space condition deliberately excludes the zero-dimensional degenerate case. -/
theorem actual_positive_origin_neighbourhood_and_local_tracking_bounds_order_constants
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [Nontrivial S]
    (X : Set S) (r delta cL cU : ℝ) (V : S → ℝ)
    (hr : 0 < r) (hball : Metric.ball (0 : S) r ⊆ X)
    (hdelta : 0 < delta) (hcontinuous : ContinuousOn V X) (hzero : V 0 = 0)
    (hlocal : ∀ x ∈ X, V x ≤ delta →
      cL * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ cU * ‖x‖ ^ 2) :
    ∃ x ∈ X, x ≠ 0 ∧ V x ≤ delta ∧ cL ≤ cU := by
  have hzeroX : (0 : S) ∈ X := hball (by simpa using hr)
  obtain ⟨s, hs, hsmall⟩ :=
    (Metric.continuousWithinAt_iff.mp (hcontinuous 0 hzeroX)) delta hdelta
  have hmin : 0 < min r s := lt_min hr hs
  have hhalf : 0 < min r s / 2 := by linarith
  obtain ⟨x, hxnorm⟩ := exists_norm_eq S hhalf.le
  have hxX : x ∈ X := hball (by
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hxnorm]
    have := min_le_left r s
    linarith)
  have hxs : dist x 0 < s := by
    rw [dist_zero_right, hxnorm]
    have := min_le_right r s
    linarith
  have hval : V x ≤ delta := by
    have hd := hsmall hxX hxs
    rw [hzero, dist_zero_right, Real.norm_eq_abs] at hd
    exact (le_abs_self (V x)).trans hd.le
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    linarith
  have hb := hlocal x hxX hval
  have horder : cL ≤ cU := by
    have hsq : 0 < ‖x‖ ^ 2 := by rw [hxnorm]; positivity
    exact (mul_le_mul_iff_left₀ hsq).mp (hb.1.trans hb.2)
  exact ⟨x, hxX, hxne, hval, horder⟩

def actualInputErosion {A : Type*} [Add A] (U W : Set A) : Set A :=
  {u | ∀ d ∈ W, u + d ∈ U}

/-- The actual Pontryagin-difference relation supplies both Assumption2 input
domain conditions. A perturbed input domain conclusion is proved here. -/
theorem actual_eroded_input_and_bounded_error_are_both_admissible
    {A : Type*} [NormedAddCommGroup A] (U : Set A) (eta : ℝ)
    (heta : 0 ≤ eta) (u d : A)
    (hu : u ∈ actualInputErosion U {e | ‖e‖ ≤ eta}) (hd : ‖d‖ ≤ eta) :
    u ∈ U ∧ u + d ∈ U := by
  constructor
  · simpa using hu 0 (by simpa using heta)
  · exact hu d hd

/-- This row calculation uses only the actual input tightening and its error
bound; it does not assume that the updated input already meets the constraints. -/
theorem actual_one_row_tightening_increment_covers_the_input_error
    (oldRow errorRow epsilonEarlier epsilonLater increment : ℝ)
    (hold : oldRow ≤ 1 - epsilonLater)
    (herror : errorRow ≤ increment)
    (hincrement : epsilonLater = epsilonEarlier + increment) :
    oldRow + errorRow ≤ 1 - epsilonEarlier := by
  linarith

end SafeLearning.CompleteCoreMPCLocalGeometry28


namespace SafeLearning.CompleteCoreMPCOrderedMargins28
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

theorem actual_nonzero_local_quadratic_tracking_bounds_order_the_constants
    {S : Type*} [NormedAddCommGroup S] (x z : S) (value cL cU : ℝ)
    (hne : x ≠ z) (hlower : cL * ‖x-z‖^2 ≤ value)
    (hupper : value ≤ cU * ‖x-z‖^2) : cL ≤ cU := by
  have hpositive : 0 < ‖x-z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  exact (mul_le_mul_iff_left₀ hpositive).mp (hlower.trans hupper)

/-- The actual epsilon formula supplies the first state-row margin once the
original positive quadratic constants are ordered. No margin conclusion is
put into a certificate premise. Deriving that order from arbitrary state-set
geometry remains a separate issue for the full theorem. -/
theorem actual_original_epsilon_formula_covers_the_first_state_row_radius
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (H : Matrix J I ℝ) (Lt : Matrix L K ℝ) (lambda eta cL cU kmax : ℝ)
    (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) (hcL : 0 < cL)
    (horder : cL ≤ cU) :
    ‖H‖ * (lambda*eta) ≤ eta*lambda*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*kmax) := by
  have hratio : 1 ≤ cU/cL := (le_div_iff₀ hcL).2 (by simpa using horder)
  have hnonneg : 0 ≤ cU/cL := le_trans (by norm_num) hratio
  have hscale : 1 ≤ Real.sqrt (cU/cL) := by
    nlinarith [Real.sqrt_nonneg (cU/cL),Real.sq_sqrt hnonneg]
  have hrow : ‖H‖ ≤ ‖H‖*Real.sqrt (cU/cL) := by
    nlinarith [norm_nonneg H]
  have hmax : ‖H‖*Real.sqrt (cU/cL) ≤ max ‖H‖ (‖Lt‖*kmax)*Real.sqrt (cU/cL) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  calc
    ‖H‖*(lambda*eta) ≤ (max ‖H‖ (‖Lt‖*kmax)*Real.sqrt (cU/cL))*(lambda*eta) :=
      mul_le_mul_of_nonneg_right (hrow.trans hmax) (mul_nonneg hlambda heta)
    _ = eta*lambda*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*kmax) := by ring
end SafeLearning.CompleteCoreMPCOrderedMargins28


namespace SafeLearning.CompleteCoreMPCActualMatrixRows28
open SafeLearning.CompleteCoreMPCNormBridge27
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- The state uses its actual Euclidean norm; the bound is the source's
matrix infinity row-sum norm, with the coordinate conversion proved. -/
def actualStateRow {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix J I ℝ) (j : J) : EuclideanSpace ℝ I →L[ℝ] ℝ :=
  let row : EuclideanSpace ℝ I →ₗ[ℝ] ℝ :=
    (LinearMap.proj j).comp ((Matrix.mulVecLin H).comp
      (WithLp.linearEquiv 2 ℝ (I → ℝ)).toLinearMap)
  row.mkContinuous ‖H‖ (by
    intro x
    change ‖(H *ᵥ (fun i => x i)) j‖ ≤ ‖H‖ * ‖x‖
    rw [Real.norm_eq_abs]
    exact actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H x j)

/-- Inputs use the actual infinity norm, rather than an unmentioned
Euclidean replacement of the disturbance/error domain. -/
def actualInputRow {K L : Type*} [Fintype K] [Fintype L]
    (Lt : Matrix L K ℝ) (j : L) : (K → ℝ) →L[ℝ] ℝ :=
  let row : (K → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj j).comp (Matrix.mulVecLin Lt)
  row.mkContinuous ‖Lt‖ (by
    intro u
    change ‖(Lt *ᵥ u) j‖ ≤ ‖Lt‖ * ‖u‖
    exact (norm_le_pi_norm (Lt *ᵥ u) j).trans (Matrix.linfty_opNorm_mulVec Lt u))

theorem actual_state_matrix_rows_have_exact_evaluation_and_derived_operator_bound
    {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix J I ℝ) (j : J) :
    (∀ x, actualStateRow H j x = (H *ᵥ (fun i => x i)) j) ∧
    ‖actualStateRow H j‖ ≤ ‖H‖ := by
  refine ⟨fun _ => rfl, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H) ?_⟩
  intro x
  change ‖(H *ᵥ (fun i => x i)) j‖ ≤ ‖H‖ * ‖x‖
  rw [Real.norm_eq_abs]
  exact actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H x j

theorem actual_input_matrix_rows_have_exact_evaluation_and_derived_operator_bound
    {K L : Type*} [Fintype K] [Fintype L]
    (Lt : Matrix L K ℝ) (j : L) :
    (∀ u, actualInputRow Lt j u = (Lt *ᵥ u) j) ∧
    ‖actualInputRow Lt j‖ ≤ ‖Lt‖ := by
  refine ⟨fun _ => rfl, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Lt) ?_⟩
  intro u
  change ‖(Lt *ᵥ u) j‖ ≤ ‖Lt‖ * ‖u‖
  exact (norm_le_pi_norm (Lt *ᵥ u) j).trans (Matrix.linfty_opNorm_mulVec Lt u)

theorem actual_state_row_polytope_is_the_original_matrix_inequality
    {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix J I ℝ) (epsilon : ℝ) :
    {x : EuclideanSpace ℝ I | ∀ j, actualStateRow H j x ≤ 1-epsilon} =
      {x | ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1-epsilon} := by
  rfl

theorem actual_input_row_polytope_is_the_original_matrix_inequality
    {K L : Type*} [Fintype K] [Fintype L]
    (Lt : Matrix L K ℝ) (epsilon : ℝ) :
    {u : K → ℝ | ∀ j, actualInputRow Lt j u ≤ 1-epsilon} =
      {u | ∀ j, (Lt *ᵥ u) j ≤ 1-epsilon} := by
  rfl

end SafeLearning.CompleteCoreMPCActualMatrixRows28


namespace SafeLearning.CompleteCoreMPCBootstrapRecursive28
open SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCExactTightening28
open SafeLearning.CompleteCoreMPCActualMatrixRows28
open SafeLearning.CompleteCoreMPCLocalGeometry28
open SafeLearning.CompleteCoreMPCOrderedMargins28
open SafeLearning.CompleteCoreMPCNormBridge27
open SafeLearning.CompleteCoreMPCFirstSuccessor27
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- The original feasible plan, original input erosion, Assumptions2/3 and
local continuity/quadratic bounds derive the first disturbed successor's
membership and local value; the typed one-step contraction then constructs
all new prediction constraints. No new-state or new-plan feasibility premise
is supplied. The zero-dimensional state case is handled directly. -/
theorem actual_original_assumptions_and_old_plan_derive_disturbed_successor_feasibility
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (H : Matrix J I ℝ) (Lt : Matrix L K ℝ)
    (X : Set (EuclideanSpace ℝ I)) (U : Set (K → ℝ))
    (f : EuclideanSpace ℝ I → (K → ℝ) → EuclideanSpace ℝ I)
    (tracking : EuclideanSpace ℝ I → EuclideanSpace ℝ I → (K → ℝ) → (K → ℝ))
    (V : EuclideanSpace ℝ I → EuclideanSpace ℝ I → (K → ℝ) → ℝ)
    (cL delta k rho cU lambda eta : ℝ)
    (certificate : TypedLocalIncrementalCertificate X U f tracking V cL delta k rho)
    (hcU : 0 < cU) (hlambda : 0 < lambda) (heta : 0 ≤ eta)
    (hsmall : eta ≤ lambda⁻¹ * Real.sqrt (delta/cU))
    (hX : ∀ x, x ∈ X ↔ ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1)
    (hUt : ∀ u, (∀ j, (Lt *ᵥ u) j ≤ 1) ↔
      u ∈ actualInputErosion U {d | ‖d‖ ≤ eta})
    (hLipschitz : ∀ x ∈ X, ∀ u ∈ U, ∀ d : K → ℝ, u+d ∈ U →
      ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖)
    (hcontinuous : ∀ z ∈ X, ∀ v ∈ U, ContinuousOn (fun y => V y z v) X)
    (hzero : ∀ z ∈ X, ∀ v ∈ U, V z z v=0)
    (hupper : ∀ y ∈ X, ∀ z ∈ X, ∀ v ∈ U,
      V y z v ≤ delta → V y z v ≤ cU * ‖y-z‖^2)
    (terminal : Set (EuclideanSpace ℝ I)) (terminalControl : EuclideanSpace ℝ I → (K → ℝ))
    (N : ℕ) (hN : 0 < N) (initial : EuclideanSpace ℝ I)
    (plan : FiniteFeasiblePrediction f (actualStateRow H) (actualInputRow Lt)
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
      terminal N initial)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, (H *ᵥ (fun i => x i)) row ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho N) ∧
      (∀ row, (Lt *ᵥ terminalControl x) row ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho N))
    (hterminalRobust : ∀ x ∈ terminal, ∀ w : EuclideanSpace ℝ I,
      ‖w‖ ≤ Real.sqrt (rho^N*cU/cL)*lambda*eta →
      f x (terminalControl x)+w ∈ terminal)
    (d : K → ℝ) (hd : ‖d‖ ≤ eta) :
    plan.input 0 ∈ U ∧ plan.input 0+d ∈ U ∧
    Nonempty (FiniteFeasiblePrediction f (actualStateRow H) (actualInputRow Lt)
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
      terminal N (f initial (plan.input 0+d))) := by
  let epsilon := lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)
  have hinc := fun j => actual_original_max_norm_tightening_covers_both_tracking_rows
    rho cL cU lambda eta ‖H‖ ‖Lt‖ k j certificate.cL_pos hcU.le hlambda.le heta
    (norm_nonneg H) (norm_nonneg Lt) certificate.k_nonneg
  have hepsilon : 0 ≤ epsilon := (hinc 0).1
  have he : ∀ j ≤ N, 0 ≤ originalTightening epsilon rho j := by
    intro j _
    exact (actual_original_tightening_has_exact_increments_and_is_monotone epsilon rho hepsilon).1 j
  have hrowX : ∀ x, x ∈ X ↔ ∀ row, actualStateRow H row x ≤ 1 := hX
  have hrowUt : ∀ u, (∀ row, actualInputRow Lt row u ≤ 1) → u ∈ U := by
    intro u hu
    exact (actual_eroded_input_and_bounded_error_are_both_admissible U eta heta u 0
      ((hUt u).1 hu) (by simpa using heta)).1
  have hradius := fun j => actual_original_radius_has_the_exact_geometric_value_budget
    rho cL cU lambda eta j certificate.rho_nonneg certificate.cL_pos hcU.le hlambda.le heta
  have hrobust : ∀ x ∈ terminal, ∀ w : EuclideanSpace ℝ I,
      ‖w‖ ≤ originalTrackingRadius rho cL cU lambda eta N →
      f x (terminalControl x)+w ∈ terminal := by
    intro x hx w hw
    exact hterminalRobust x hx w (by
      rwa [actual_geometric_tracking_radius_is_the_printed_terminal_ball_radius
        rho cL cU lambda eta N certificate.rho_nonneg certificate.cL_pos hcU.le] at hw)
  have hinvariant : ∀ x ∈ terminal, f x (terminalControl x) ∈ terminal := by
    intro x hx
    simpa using hrobust x hx 0 (by simpa using (hradius N).1)
  have href := actual_old_feasible_plan_supplies_every_shifted_reference_assumption
    plan terminalControl X U hrowX hrowUt he hterminalRows hinvariant
  dsimp at href
  have hx : initial ∈ X := by
    apply (hX initial).2
    intro row
    have hh := plan.state_constraints 0 hN row
    change (H *ᵥ (fun i => plan.state 0 i)) row ≤ 1-_ at hh
    simpa [originalTightening,plan.initial_eq] using hh
  have hurows : ∀ row, (Lt *ᵥ plan.input 0) row ≤ 1 := by
    intro row
    have hh := plan.input_constraints 0 hN row
    change (Lt *ᵥ plan.input 0) row ≤ 1-_ at hh
    simpa [originalTightening] using hh
  have hinputs := actual_eroded_input_and_bounded_error_are_both_admissible U eta heta
    (plan.input 0) d ((hUt _).1 hurows) hd
  have hnominal : oldPlanExtendedState plan terminalControl 1=f initial (plan.input 0) := by
    have hh := actual_old_feasible_plan_extends_by_the_terminal_plant_step plan terminalControl 0 (by omega)
    simpa [oldPlanExtendedState,oldPlanExtendedInput,hN,plan.initial_eq] using hh
  have hvnext := href.2.1 0 (by omega)
  have hzX := href.1 0 (by omega)
  have hbootstrap : f initial (plan.input 0+d) ∈ X ∧
      V (f initial (plan.input 0+d)) (oldPlanExtendedState plan terminalControl 1)
        (oldPlanExtendedInput plan terminalControl 1) ≤ cU*(lambda*eta)^2 := by
    rcases subsingleton_or_nontrivial (EuclideanSpace ℝ I) with hs | hns
    · letI := hs
      have heq : f initial (plan.input 0+d)=oldPlanExtendedState plan terminalControl 1 :=
        Subsingleton.elim _ _
      refine ⟨by simpa [heq] using hzX, ?_⟩
      rw [heq,hzero _ hzX _ hvnext]
      positivity
    · letI := hns
      have hzeroX : (0 : EuclideanSpace ℝ I) ∈ X := (hX 0).2 (by
        intro j
        change (H *ᵥ (0 : I → ℝ)) j ≤ 1
        simp)
      have hball := actual_polytopic_state_set_contains_an_explicit_positive_origin_ball H
      have hballX : Metric.ball (0 : EuclideanSpace ℝ I) (1/(‖H‖+1)) ⊆ X := by
        intro x hh
        exact (hX x).2 (hball.2 hh)
      obtain ⟨_,_,_,_,horder⟩ :=
        actual_positive_origin_neighbourhood_and_local_tracking_bounds_order_constants
          X (1/(‖H‖+1)) delta cL cU (fun y => V y 0 (oldPlanExtendedInput plan terminalControl 1))
          hball.1 hballX certificate.delta_pos (hcontinuous _ hzeroX _ hvnext)
          (hzero _ hzeroX _ hvnext) (by
            intro y hy hvalue
            simpa only [sub_zero,Nat.zero_add] using
              And.intro (certificate.lower y hy 0 hzeroX _ hvnext hvalue)
                (hupper y hy 0 hzeroX _ hvnext hvalue))
      have hmargin : ‖H‖*(lambda*eta) ≤ epsilon := by
        simpa [epsilon,mul_comm,mul_left_comm,mul_assoc] using
          actual_original_epsilon_formula_covers_the_first_state_row_radius
            H Lt lambda eta cL cU k hlambda.le heta certificate.cL_pos horder
      have hnominalRows : ∀ row, (H *ᵥ (fun i => f initial (plan.input 0) i)) row ≤ 1-epsilon := by
        intro row
        have hh := href.2.2.2.1 0 hN row
        change (H *ᵥ (fun i => oldPlanExtendedState plan terminalControl (0+1) i)) row ≤ 1-_ at hh
        simpa [hnominal,originalTightening,epsilon] using hh
      have hb := actual_first_disturbed_successor_is_in_X_and_in_the_local_tracking_sublevel
        H f U lambda eta delta cU epsilon hlambda heta certificate.delta_pos hcU hepsilon hsmall hmargin
        (by intro x hx u hu d hud; exact hLipschitz x ((hX x).2 hx) u hu d hud)
        initial (plan.input 0) d (oldPlanExtendedInput plan terminalControl 1)
        ((hX initial).1 hx) hinputs.1 hinputs.2 hvnext hd hnominalRows V
        (by
          intro z hz v hv
          exact (hcontinuous z ((hX z).2 hz) v hv).mono (fun y hy => (hX y).2 hy))
        (by intro z hz v hv; exact hzero z ((hX z).2 hz) v hv)
        (by intro y hy z hz v hv hvalue; exact hupper y ((hX y).2 hy) z ((hX z).2 hz) v hv hvalue)
      exact ⟨(hX _).2 hb.1,by simpa [hnominal] using hb.2.1⟩
  refine ⟨hinputs.1,hinputs.2,?_⟩
  exact actual_old_feasible_plan_and_source_budgets_construct_a_true_shifted_prediction
    X U f tracking V (actualStateRow H) (actualInputRow Lt)
    cL delta k rho cU lambda eta ‖H‖ ‖Lt‖ certificate hcU.le hlambda.le heta
    (norm_nonneg H) (norm_nonneg Lt)
    (actual_positive_lipschitz_assumption_three_implies_the_squared_local_budget
      lambda eta delta cU hlambda heta certificate.delta_pos hcU hsmall)
    (fun row => (actual_state_matrix_rows_have_exact_evaluation_and_derived_operator_bound H row).2)
    (fun row => (actual_input_matrix_rows_have_exact_evaluation_and_derived_operator_bound Lt row).2)
    terminal terminalControl N initial (f initial (plan.input 0+d)) plan hrowX hrowUt
    hterminalRows hrobust hbootstrap.1 hbootstrap.2

end SafeLearning.CompleteCoreMPCBootstrapRecursive28

namespace SafeLearning.CompleteCoreMPCOriginalFeedbackNorm28
open SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCNormBridge27

/-- The source's Euclidean feedback-deviation bound implies the actual input
infinity bound needed by the tightened-input construction. Original state
and input domain quantifiers are preserved, including the explicitly adopted
local successor-domain clause. No all-stage feasibility conclusion is a
premise of this conversion. -/
theorem actual_original_euclidean_feedback_bounds_construct_the_input_infinity_certificate
    {S K : Type*} [NormedAddCommGroup S] [Fintype K]
    (X : Set S) (U : Set (K → ℝ)) (f : S → (K → ℝ) → S)
    (tracking : S → S → (K → ℝ) → (K → ℝ)) (V : S → S → (K → ℝ) → ℝ)
    (cL delta k rho : ℝ) (hcL : 0 < cL) (hdelta : 0 < delta)
    (hk : 0 ≤ k) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hlower : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
      V x z v ≤ delta → cL * ‖x-z‖^2 ≤ V x z v)
    (hfeedbackEuclidean : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
      V x z v ≤ delta →
      ‖WithLp.toLp 2 (tracking x z v-v)‖ ≤ k * ‖x-z‖)
    (hcontract : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
      ∀ vnext ∈ U, f z v ∈ X → V x z v ≤ delta →
      f x (tracking x z v) ∈ X ∧
      V (f x (tracking x z v)) (f z v) vnext ≤ rho * V x z v) :
    TypedLocalIncrementalCertificate X U f tracking V cL delta k rho := by
  refine ⟨hcL,hdelta,hk,hrho,hrho1,hlower,?_,hcontract⟩
  intro x hx z hz v hv hvalue
  have hcoordinate := actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm
    (WithLp.toLp 2 (tracking x z v-v))
  change ‖tracking x z v-v‖ ≤ ‖WithLp.toLp 2 (tracking x z v-v)‖ at hcoordinate
  exact hcoordinate.trans (hfeedbackEuclidean x hx z hz v hv hvalue)

end SafeLearning.CompleteCoreMPCOriginalFeedbackNorm28

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteCoreMPCFiniteOptimizer28

variable {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

abbrev Plan (S A : Type*) (N : ℕ) := (Fin (N+1) → S) × (Fin N → A)

/-- The actual finite-horizon optimization constraints, with no compact-domain
membership inserted into this definition. Dynamics, stage rows and terminal
membership are exactly the original prediction constraints. -/
def originalFeasiblePlans (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) : Set (Plan S A N) :=
  {p | p.1 0 = initial ∧
    (∀ j : Fin N, p.1 j.succ = f (p.1 j.castSucc) (p.2 j)) ∧
    (∀ j : Fin N, ∀ row, stateRow row (p.1 j.castSucc) ≤ 1-epsilon j) ∧
    (∀ j : Fin N, ∀ row, inputRow row (p.2 j) ≤ 1-epsilon j) ∧
    p.1 (Fin.last N) ∈ terminal}

/-- Domain membership is derived from actual row definitions and nonnegative
tightening. The terminal-subset hypothesis is the separate actual terminal
constraint ingredient; it is not recursive shifted feasibility. -/
theorem actual_original_rows_derive_all_prediction_domain_membership
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminal : terminal ⊆ X)
    (p : Plan S A N)
    (hp : p ∈ originalFeasiblePlans N initial f stateRow inputRow epsilon terminal) :
    (∀ j, p.1 j ∈ X) ∧ (∀ j, p.2 j ∈ U) := by
  constructor
  · intro j
    by_cases hj : j.val < N
    · let k : Fin N := ⟨j.val,hj⟩
      have heq : k.castSucc = j := by ext; rfl
      apply (hX _).mpr
      intro row
      have hh := hp.2.2.1 k row
      rw [heq] at hh
      linarith [hepsilon k]
    · have heq : j = Fin.last N := by
        ext
        simp only [Fin.val_last]
        omega
      rw [heq]
      exact hterminal hp.2.2.2.2
  · intro j
    apply hU
    intro row
    have hh := hp.2.2.2.1 j row
    linarith [hepsilon j]

/-- The source terminal row ingredient itself derives terminal subset X;
nonnegative epsilon_N is taken from the actual tightening formula. No sign
is inferred from membership in a negatively scaled set. -/
theorem actual_terminal_row_ingredient_derives_state_domain
    (stateRow : J → S →L[ℝ] ℝ) (X terminal : Set S) (epsilonN : ℝ)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hepsilonN : 0 ≤ epsilonN)
    (hrows : ∀ x ∈ terminal, ∀ row, stateRow row x ≤ 1-epsilonN) :
    terminal ⊆ X := by
  intro x hx
  apply (hX x).mpr
  intro row
  have hh := hrows x hx row
  linarith

theorem actual_original_finite_prediction_constraints_are_closed
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal) :
    IsClosed (originalFeasiblePlans N initial f stateRow inputRow epsilon terminal) := by
  have hi : IsClosed {p : Plan S A N | p.1 0 = initial} :=
    isClosed_eq ((continuous_apply 0).comp continuous_fst) continuous_const
  have hd : IsClosed {p : Plan S A N | ∀ j : Fin N,
      p.1 j.succ = f (p.1 j.castSucc) (p.2 j)} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    have hp : Continuous (fun p : Plan S A N => (p.1 j.castSucc,p.2 j)) :=
      (((continuous_apply j.castSucc).comp continuous_fst).prodMk
        ((continuous_apply j).comp continuous_snd))
    have hh : Continuous (fun p : Plan S A N => f (p.1 j.castSucc) (p.2 j)) := by
      simpa only [Function.comp_def] using hf.comp hp
    exact isClosed_eq ((continuous_apply j.succ).comp continuous_fst) hh
  have hx : IsClosed {p : Plan S A N | ∀ j : Fin N, ∀ row,
      stateRow row (p.1 j.castSucc) ≤ 1-epsilon j} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro row
    exact isClosed_le ((stateRow row).continuous.comp
      ((continuous_apply j.castSucc).comp continuous_fst)) continuous_const
  have hu : IsClosed {p : Plan S A N | ∀ j : Fin N, ∀ row,
      inputRow row (p.2 j) ≤ 1-epsilon j} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro row
    exact isClosed_le ((inputRow row).continuous.comp
      ((continuous_apply j).comp continuous_snd)) continuous_const
  have ht : IsClosed {p : Plan S A N | p.1 (Fin.last N) ∈ terminal} :=
    hterminal.preimage ((continuous_apply (Fin.last N)).comp continuous_fst)
  exact hi.inter (hd.inter (hx.inter (hu.inter ht)))

theorem actual_original_feasible_prediction_set_is_compact
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminalX : terminal ⊆ X)
    (hcompactX : IsCompact X) (hcompactU : IsCompact U)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal) :
    IsCompact (originalFeasiblePlans N initial f stateRow inputRow epsilon terminal) := by
  have hx : IsCompact {xs : Fin (N+1) → S | ∀ j, xs j ∈ X} :=
    isCompact_pi_infinite (fun _ => hcompactX)
  have hu : IsCompact {us : Fin N → A | ∀ j, us j ∈ U} :=
    isCompact_pi_infinite (fun _ => hcompactU)
  have hdomain := hx.prod hu
  apply hdomain.of_isClosed_subset
    (actual_original_finite_prediction_constraints_are_closed N initial f stateRow inputRow
      epsilon terminal hf hterminal)
  intro p hp
  have hd := actual_original_rows_derive_all_prediction_domain_membership
    N initial f stateRow inputRow epsilon terminal X U hX hU hepsilon hterminalX p hp
  exact hd

/-- The finite sum is the original horizon cost; no optimality or minimizing
sequence is supplied as a premise. -/
def originalFiniteObjective (N : ℕ) (stageCost : S → A → ℝ)
    (terminalCost : S → ℝ) (p : Plan S A N) : ℝ :=
  (∑ j : Fin N, stageCost (p.1 j.castSucc) (p.2 j)) +
    terminalCost (p.1 (Fin.last N))

theorem actual_original_finite_objective_is_continuous
    (N : ℕ) (stageCost : S → A → ℝ) (terminalCost : S → ℝ)
    (hstage : Continuous (fun z : S × A => stageCost z.1 z.2))
    (hterminalCost : Continuous terminalCost) :
    Continuous (originalFiniteObjective N stageCost terminalCost) := by
  unfold originalFiniteObjective
  apply Continuous.add
  · apply continuous_finsetSum
    intro j _
    have hp : Continuous (fun p : Plan S A N => (p.1 j.castSucc,p.2 j)) :=
      (((continuous_apply j.castSucc).comp continuous_fst).prodMk
        ((continuous_apply j).comp continuous_snd))
    simpa only [Function.comp_def] using hstage.comp hp
  · exact hterminalCost.comp ((continuous_apply (Fin.last N)).comp continuous_fst)

theorem actual_original_finite_horizon_feasibility_implies_attained_global_minimum
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminalX : terminal ⊆ X)
    (hcompactX : IsCompact X) (hcompactU : IsCompact U)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal)
    (stageCost : S → A → ℝ) (terminalCost : S → ℝ)
    (hstage : Continuous (fun z : S × A => stageCost z.1 z.2))
    (hterminalCost : Continuous terminalCost)
    (hfeasible : (originalFeasiblePlans N initial f stateRow inputRow epsilon terminal).Nonempty) :
    ∃ p ∈ originalFeasiblePlans N initial f stateRow inputRow epsilon terminal,
      ∀ q ∈ originalFeasiblePlans N initial f stateRow inputRow epsilon terminal,
        originalFiniteObjective N stageCost terminalCost p ≤
          originalFiniteObjective N stageCost terminalCost q := by
  exact (actual_original_feasible_prediction_set_is_compact N initial f stateRow inputRow
    epsilon terminal X U hX hU hepsilon hterminalX hcompactX hcompactU hf hterminal).exists_isMinOn
      hfeasible (actual_original_finite_objective_is_continuous N stageCost terminalCost
        hstage hterminalCost).continuousOn

/-- Classical selection is on the actual feasible-state domain. Feasibility
and global optimality of every selected plan are derived by the preceding
compactness theorem. No measurable-selector conclusion is asserted. -/
theorem actual_original_feasible_state_domain_has_a_classically_chosen_optimizer
    (N : ℕ) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminalX : terminal ⊆ X)
    (hcompactX : IsCompact X) (hcompactU : IsCompact U)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal)
    (stageCost : S → A → ℝ) (terminalCost : S → ℝ)
    (hstage : Continuous (fun z : S × A => stageCost z.1 z.2))
    (hterminalCost : Continuous terminalCost) :
    ∃ pick : {x : S // (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty} →
        Plan S A N,
      ∀ x, pick x ∈ originalFeasiblePlans N x.val f stateRow inputRow epsilon terminal ∧
        ∀ q ∈ originalFeasiblePlans N x.val f stateRow inputRow epsilon terminal,
          originalFiniteObjective N stageCost terminalCost (pick x) ≤
            originalFiniteObjective N stageCost terminalCost q := by
  classical
  have hmin := fun x : {x : S //
      (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty} =>
    actual_original_finite_horizon_feasibility_implies_attained_global_minimum
      N x.val f stateRow inputRow epsilon terminal X U hX hU hepsilon hterminalX
      hcompactX hcompactU hf hterminal stageCost terminalCost hstage hterminalCost x.property
  choose pick hp using hmin
  exact ⟨pick,hp⟩

/-- The actual MPC policy is the first input of a chosen attained optimizer,
under the physical positive-horizon requirement. It remains a classical
choice; probability arguments need their own measurable outcome premise. -/
theorem actual_positive_horizon_mpc_first_input_is_a_chosen_optimal_input
    (N : ℕ) (hN : 0 < N) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminalX : terminal ⊆ X)
    (hcompactX : IsCompact X) (hcompactU : IsCompact U)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal)
    (stageCost : S → A → ℝ) (terminalCost : S → ℝ)
    (hstage : Continuous (fun z : S × A => stageCost z.1 z.2))
    (hterminalCost : Continuous terminalCost) :
    ∃ policy : {x : S // (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty} → A,
      ∀ x, ∃ p ∈ originalFeasiblePlans N x.val f stateRow inputRow epsilon terminal,
        policy x = p.2 ⟨0,hN⟩ ∧
        ∀ q ∈ originalFeasiblePlans N x.val f stateRow inputRow epsilon terminal,
          originalFiniteObjective N stageCost terminalCost p ≤
            originalFiniteObjective N stageCost terminalCost q := by
  obtain ⟨pick,hpick⟩ :=
    actual_original_feasible_state_domain_has_a_classically_chosen_optimizer
      N f stateRow inputRow epsilon terminal X U hX hU hepsilon hterminalX
      hcompactX hcompactU hf hterminal stageCost terminalCost hstage hterminalCost
  exact ⟨fun x => (pick x).2 ⟨0,hN⟩, fun x =>
    ⟨pick x,(hpick x).1,rfl,(hpick x).2⟩⟩

end SafeLearning.CompleteCoreMPCFiniteOptimizer28

namespace SafeLearning.CompleteCoreMPCOriginalQuadraticCost28
open scoped Matrix

def originalQuadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ x ((Matrix.toEuclideanLin M).toContinuousLinearMap x)

/-- Continuity is true for the actual printed matrix quadratic form. Positive
 definiteness is needed for the later stability argument, not attainment. -/
theorem actual_original_matrix_quadratic_cost_is_continuous
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (originalQuadratic M) := by
  exact continuous_id.inner ((Matrix.toEuclideanLin M).toContinuousLinearMap.continuous)

theorem actual_original_Q_R_stage_and_P_terminal_costs_are_continuous
    {n m : ℕ} (Q P : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      originalQuadratic Q z.1 + originalQuadratic R z.2) ∧
    Continuous (originalQuadratic P) := by
  exact ⟨((actual_original_matrix_quadratic_cost_is_continuous Q).comp continuous_fst).add
    ((actual_original_matrix_quadratic_cost_is_continuous R).comp continuous_snd),
    actual_original_matrix_quadratic_cost_is_continuous P⟩

end SafeLearning.CompleteCoreMPCOriginalQuadraticCost28


namespace SafeLearning.CompleteCoreMPCFinitePredictionConnection28
open SafeLearning.CompleteCoreMPCFiniteOptimizer28
open SafeLearning.CompleteCoreMPCTypedDomainShift28
variable {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def finiteStateExtension (N : ℕ) (p : Plan S A N) (j : ℕ) : S :=
  if hj : j < N+1 then p.1 ⟨j,hj⟩ else 0
def finiteInputExtension (N : ℕ) (p : Plan S A N) (j : ℕ) : A :=
  if hj : j < N then p.2 ⟨j,hj⟩ else 0

theorem actual_finite_state_extension_recovers_every_prediction_coordinate
    (N : ℕ) (p : Plan S A N) (j : Fin (N+1)) :
    finiteStateExtension N p j.val = p.1 j := by
  simp [finiteStateExtension,j.isLt]

theorem actual_finite_input_extension_recovers_every_prediction_coordinate
    (N : ℕ) (p : Plan S A N) (j : Fin N) :
    finiteInputExtension N p j.val = p.2 j := by
  simp [finiteInputExtension,j.isLt]

/-- Finite optimizer variables produce the exact original Nat-indexed
prediction used by the already-proved shifted constructor. The extension
outside the horizon is irrelevant to its constraints and is replaced by the
actual terminal-controller extension in that constructor. -/
def originalFinitePlanToNativePrediction
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) (p : Plan S A N)
    (hp : p ∈ originalFeasiblePlans N initial f stateRow inputRow epsilon terminal) :
    FiniteFeasiblePrediction f stateRow inputRow epsilon terminal N initial where
  state := finiteStateExtension N p
  input := finiteInputExtension N p
  initial_eq := by simpa [finiteStateExtension] using hp.1
  dynamics := by
    intro j hj
    have hjnext : j+1 < N+1 := by omega
    have hjstate : j < N+1 := by omega
    simpa [finiteStateExtension,finiteInputExtension,hj,hjnext,hjstate] using hp.2.1 ⟨j,hj⟩
  state_constraints := by
    intro j hj row
    have hjstate : j < N+1 := by omega
    simpa [finiteStateExtension,hjstate] using hp.2.2.1 ⟨j,hj⟩ row
  input_constraints := by
    intro j hj row
    simpa [finiteInputExtension,hj] using hp.2.2.2.1 ⟨j,hj⟩ row
  terminal_constraint := by
    change finiteStateExtension N p N ∈ terminal
    have hlast : N < N+1 := by omega
    rw [finiteStateExtension,dif_pos hlast]
    exact hp.2.2.2.2

def nativePredictionToOriginalFinitePlan
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S)
    (p : FiniteFeasiblePrediction f stateRow inputRow epsilon terminal N initial) :
    Plan S A N := (fun j => p.state j,fun j => p.input j)

theorem actual_native_prediction_supplies_every_original_finite_optimizer_constraint
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S)
    (p : FiniteFeasiblePrediction f stateRow inputRow epsilon terminal N initial) :
    nativePredictionToOriginalFinitePlan N initial f stateRow inputRow epsilon terminal p ∈
      originalFeasiblePlans N initial f stateRow inputRow epsilon terminal := by
  refine ⟨p.initial_eq,?_,?_,?_,p.terminal_constraint⟩
  · intro j
    simpa [nativePredictionToOriginalFinitePlan] using p.dynamics j.val j.isLt
  · intro j row
    exact p.state_constraints j.val j.isLt row
  · intro j row
    exact p.input_constraints j.val j.isLt row

theorem actual_finite_optimizer_and_shifted_constructor_have_the_same_feasible_state_domain
    (N : ℕ) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) :
    (originalFeasiblePlans N initial f stateRow inputRow epsilon terminal).Nonempty ↔
      Nonempty (FiniteFeasiblePrediction f stateRow inputRow epsilon terminal N initial) := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨originalFinitePlanToNativePrediction N initial f stateRow inputRow epsilon terminal p hp⟩
  · rintro ⟨p⟩
    exact ⟨nativePredictionToOriginalFinitePlan N initial f stateRow inputRow epsilon terminal p,
      actual_native_prediction_supplies_every_original_finite_optimizer_constraint
        N initial f stateRow inputRow epsilon terminal p⟩

theorem actual_positive_horizon_optimizer_first_input_matches_the_shifted_constructor
    (N : ℕ) (hN : 0 < N) (initial : S) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) (p : Plan S A N)
    (hp : p ∈ originalFeasiblePlans N initial f stateRow inputRow epsilon terminal) :
    (originalFinitePlanToNativePrediction N initial f stateRow inputRow epsilon terminal p hp).input 0 =
      p.2 ⟨0,hN⟩ := by
  simp [originalFinitePlanToNativePrediction,finiteInputExtension,hN]

end SafeLearning.CompleteCoreMPCFinitePredictionConnection28


namespace SafeLearning.CompleteCoreMPCGlobalOptimizerCertificate28
open SafeLearning.CompleteCoreMPCFiniteOptimizer28
open SafeLearning.CompleteCoreMPCFinitePredictionConnection28
open SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCExactTightening28
open SafeLearning.CompleteCoreMPCActualMatrixRows28
open SafeLearning.CompleteCoreMPCBootstrapRecursive28
open SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open SafeLearning.CompleteCoreMPCLocalGeometry28
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- A total classical MPC function is obtained from actual attained original
optimizers on the feasible-state domain. The zero extension outside that
domain makes no feasibility or measurability claim there. -/
theorem actual_attained_original_optimizers_supply_a_total_first_input_policy
    {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (N : ℕ) (hN : 0 < N) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (U : Set A)
    (hX : ∀ x, x ∈ X ↔ ∀ row, stateRow row x ≤ 1)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hepsilon : ∀ j : Fin N, 0 ≤ epsilon j)
    (hterminalX : terminal ⊆ X)
    (hcompactX : IsCompact X) (hcompactU : IsCompact U)
    (hf : Continuous (fun z : S × A => f z.1 z.2))
    (hterminal : IsClosed terminal)
    (stageCost : S → A → ℝ) (terminalCost : S → ℝ)
    (hstage : Continuous (fun z : S × A => stageCost z.1 z.2))
    (hterminalCost : Continuous terminalCost) :
    ∃ mpc : S → A, ∀ x,
      (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty →
      ∃ p ∈ originalFeasiblePlans N x f stateRow inputRow epsilon terminal,
        mpc x = p.2 ⟨0,hN⟩ ∧
        ∀ q ∈ originalFeasiblePlans N x f stateRow inputRow epsilon terminal,
          originalFiniteObjective N stageCost terminalCost p ≤
            originalFiniteObjective N stageCost terminalCost q := by
  classical
  obtain ⟨pick,hpick⟩ :=
    actual_original_feasible_state_domain_has_a_classically_chosen_optimizer
      N f stateRow inputRow epsilon terminal X U hX hU hepsilon hterminalX
      hcompactX hcompactU hf hterminal stageCost terminalCost hstage hterminalCost
  let mpc : S → A := fun x =>
    if hx : (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty
    then (pick ⟨x,hx⟩).2 ⟨0,hN⟩ else 0
  refine ⟨mpc,?_⟩
  intro x hx
  refine ⟨pick ⟨x,hx⟩,(hpick ⟨x,hx⟩).1,?_,(hpick ⟨x,hx⟩).2⟩
  simp [mpc,hx]

/-- The actual input of a feasible original prediction suffices for the
robust certificate, since the bootstrap constructs every next prediction
constraint. Optimality is supplied separately by the previous theorem.
No disturbed-successor or shifted-plan feasibility is assumed. -/
theorem actual_original_prediction_choice_derives_the_robust_one_step_certificate
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (H : Matrix J I ℝ) (Lt : Matrix L K ℝ)
    (X : Set (EuclideanSpace ℝ I)) (U : Set (K → ℝ))
    (f : EuclideanSpace ℝ I → (K → ℝ) → EuclideanSpace ℝ I)
    (tracking : EuclideanSpace ℝ I → EuclideanSpace ℝ I → (K → ℝ) → (K → ℝ))
    (V : EuclideanSpace ℝ I → EuclideanSpace ℝ I → (K → ℝ) → ℝ)
    (cL delta k rho cU lambda eta : ℝ)
    (certificate : TypedLocalIncrementalCertificate X U f tracking V cL delta k rho)
    (hcU : 0 < cU) (hlambda : 0 < lambda) (heta : 0 ≤ eta)
    (hsmall : eta ≤ lambda⁻¹ * Real.sqrt (delta/cU))
    (hX : ∀ x, x ∈ X ↔ ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1)
    (hUt : ∀ u, (∀ j, (Lt *ᵥ u) j ≤ 1) ↔
      u ∈ actualInputErosion U {d | ‖d‖ ≤ eta})
    (hLipschitz : ∀ x ∈ X, ∀ u ∈ U, ∀ d : K → ℝ, u+d ∈ U →
      ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖)
    (hcontinuous : ∀ z ∈ X, ∀ v ∈ U, ContinuousOn (fun y => V y z v) X)
    (hzero : ∀ z ∈ X, ∀ v ∈ U, V z z v=0)
    (hupper : ∀ y ∈ X, ∀ z ∈ X, ∀ v ∈ U,
      V y z v ≤ delta → V y z v ≤ cU * ‖y-z‖^2)
    (terminal : Set (EuclideanSpace ℝ I))
    (terminalControl : EuclideanSpace ℝ I → (K → ℝ))
    (N : ℕ) (hN : 0 < N)
    (hterminalRows : ∀ x ∈ terminal,
      (∀ row, (H *ᵥ (fun i => x i)) row ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho N) ∧
      (∀ row, (Lt *ᵥ terminalControl x) row ≤ 1-originalTightening
        (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho N))
    (hterminalRobust : ∀ x ∈ terminal, ∀ w : EuclideanSpace ℝ I,
      ‖w‖ ≤ Real.sqrt (rho^N*cU/cL)*lambda*eta →
      f x (terminalControl x)+w ∈ terminal)
    (mpc : EuclideanSpace ℝ I → (K → ℝ))
    (hchoice : ∀ x,
      (originalFeasiblePlans N x f (actualStateRow H) (actualInputRow Lt)
        (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
        terminal).Nonempty →
      ∃ p ∈ originalFeasiblePlans N x f (actualStateRow H) (actualInputRow Lt)
        (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
        terminal, mpc x=p.2 ⟨0,hN⟩) :
    robustOneStepCertificate (fun z => f z.1 z.2) mpc
      {x | (originalFeasiblePlans N x f (actualStateRow H) (actualInputRow Lt)
        (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
        terminal).Nonempty} U eta := by
  intro x hx d hd
  obtain ⟨p,hp,hfirst⟩ := hchoice x hx
  let native := originalFinitePlanToNativePrediction N x f (actualStateRow H)
    (actualInputRow Lt)
    (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
    terminal p hp
  have hi : native.input 0=p.2 ⟨0,hN⟩ :=
    actual_positive_horizon_optimizer_first_input_matches_the_shifted_constructor
      N hN x f (actualStateRow H) (actualInputRow Lt)
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
      terminal p hp
  have next := actual_original_assumptions_and_old_plan_derive_disturbed_successor_feasibility
    H Lt X U f tracking V cL delta k rho cU lambda eta certificate hcU hlambda heta
    hsmall hX hUt hLipschitz hcontinuous hzero hupper terminal terminalControl
    N hN x native hterminalRows hterminalRobust d hd
  rw [hi,←hfirst] at next
  obtain ⟨_,hinput,⟨newPrediction⟩⟩ := next
  refine ⟨?_,hinput⟩
  exact ⟨nativePredictionToOriginalFinitePlan N (f x (mpc x+d)) f
    (actualStateRow H) (actualInputRow Lt)
    (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
    terminal newPrediction,
    actual_native_prediction_supplies_every_original_finite_optimizer_constraint
      N (f x (mpc x+d)) f (actualStateRow H) (actualInputRow Lt)
      (originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho)
      terminal newPrediction⟩

end SafeLearning.CompleteCoreMPCGlobalOptimizerCertificate28


namespace SafeLearning.CompleteCoreMPCTerminalPredictionFeasibility28
open SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCFiniteOptimizer28
open SafeLearning.CompleteCoreMPCFinitePredictionConnection28
variable {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def actualTerminalPredictionState (f : S → A → S) (control : S → A)
    (initial : S) : ℕ → S
  | 0 => initial
  | j+1 => f (actualTerminalPredictionState f control initial j)
      (control (actualTerminalPredictionState f control initial j))

/-- Genuine terminal invariance puts every terminal-control prediction in the
terminal set. The original state/input row bounds are then applicable at each
actual predicted state, not merely at the initial state. -/
theorem actual_terminal_controller_prediction_stays_in_the_terminal_set
    (f : S → A → S) (control : S → A) (terminal : Set S)
    (hinvariant : ∀ x ∈ terminal, f x (control x) ∈ terminal)
    (initial : S) (hinitial : initial ∈ terminal) :
    ∀ j, actualTerminalPredictionState f control initial j ∈ terminal := by
  intro j
  induction j with
  | zero => exact hinitial
  | succ j ih => exact hinvariant _ ih

/-- All horizon constraints of the terminal plan follow from the source
terminal rows at N and monotonicity of the exact epsilon sequence. No shifted
plan or terminal-feasible-state conclusion is supplied as a premise. -/
def actualTerminalControllerSuppliesFiniteFeasiblePrediction
    (f : S → A → S) (control : S → A)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) (N : ℕ)
    (hinvariant : ∀ x ∈ terminal, f x (control x) ∈ terminal)
    (hrows : ∀ x ∈ terminal,
      (∀ row, stateRow row x ≤ 1-epsilon N) ∧
      (∀ row, inputRow row (control x) ≤ 1-epsilon N))
    (hmono : ∀ j < N, epsilon j ≤ epsilon N)
    (initial : S) (hinitial : initial ∈ terminal) :
    FiniteFeasiblePrediction f stateRow inputRow epsilon terminal N initial where
  state := actualTerminalPredictionState f control initial
  input := fun j => control (actualTerminalPredictionState f control initial j)
  initial_eq := rfl
  dynamics := by intro j _; rfl
  state_constraints := by
    intro j hj row
    have hx := actual_terminal_controller_prediction_stays_in_the_terminal_set
      f control terminal hinvariant initial hinitial j
    exact ((hrows _ hx).1 row).trans (sub_le_sub_left (hmono j hj) 1)
  input_constraints := by
    intro j hj row
    have hx := actual_terminal_controller_prediction_stays_in_the_terminal_set
      f control terminal hinvariant initial hinitial j
    exact ((hrows _ hx).2 row).trans (sub_le_sub_left (hmono j hj) 1)
  terminal_constraint :=
    actual_terminal_controller_prediction_stays_in_the_terminal_set
      f control terminal hinvariant initial hinitial N

/-- The terminal set is a subset of the genuine original feasible-state
domain, including horizon zero. This supplies the explicit terminal-subset
interface of the selected actual hybrid-trajectory theorem. -/
theorem actual_terminal_ingredients_derive_original_mpc_feasibility
    (f : S → A → S) (control : S → A)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal : Set S) (N : ℕ)
    (hinvariant : ∀ x ∈ terminal, f x (control x) ∈ terminal)
    (hrows : ∀ x ∈ terminal,
      (∀ row, stateRow row x ≤ 1-epsilon N) ∧
      (∀ row, inputRow row (control x) ≤ 1-epsilon N))
    (hmono : ∀ j < N, epsilon j ≤ epsilon N) :
    terminal ⊆ {initial | (originalFeasiblePlans N initial f stateRow inputRow
      epsilon terminal).Nonempty} := by
  intro initial hinitial
  let prediction := actualTerminalControllerSuppliesFiniteFeasiblePrediction
    f control stateRow inputRow epsilon terminal N hinvariant hrows hmono initial hinitial
  exact ⟨nativePredictionToOriginalFinitePlan N initial f stateRow inputRow epsilon terminal prediction,
    actual_native_prediction_supplies_every_original_finite_optimizer_constraint
      N initial f stateRow inputRow epsilon terminal prediction⟩

end SafeLearning.CompleteCoreMPCTerminalPredictionFeasibility28


namespace SafeLearning.CompleteCoreMPCOriginalDomainAndSublevel28
open Filter
open scoped Topology
open SafeLearning.CompleteCoreMPCFiniteOptimizer28
open SafeLearning.CompleteCoreMPCExactTightening28
open SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open SafeLearning.CompleteLyapunovTrajectoryValidation
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- Nonnegativity and monotonicity follow from the actual source max-of-row-
norm coefficient. They do not require the false inference epsilon_N<=1
from origin membership of a negatively scaled set. -/
theorem actual_source_epsilon_is_nonnegative_and_monotone
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (H : Matrix J I ℝ) (Lt : Matrix L K ℝ)
    (lambda eta cU cL k rho : ℝ) (hlambda : 0 ≤ lambda) (heta : 0 ≤ eta) :
    let e := lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)
    (∀ j, 0 ≤ originalTightening e rho j) ∧
      Monotone (originalTightening e rho) := by
  dsimp only
  have hm : 0 ≤ max ‖H‖ (‖Lt‖*k) :=
    (norm_nonneg H).trans (le_max_left _ _)
  have he : 0 ≤ lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k) :=
    mul_nonneg (mul_nonneg (mul_nonneg hlambda heta) (Real.sqrt_nonneg _)) hm
  have h := actual_original_tightening_has_exact_increments_and_is_monotone
    (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho he
  exact ⟨h.1,h.2.2⟩

/-- Original terminal row inequalities derive actual state and input domain
membership, even when some tightening factors exceed one. -/
theorem actual_terminal_tightened_rows_derive_original_X_and_U_membership
    {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (X terminal : Set S) (U : Set A) (control : S → A)
    (epsilon : ℕ → ℝ) (N : ℕ) (hepsilon : 0 ≤ epsilon N)
    (hX : ∀ x, (∀ row, stateRow row x ≤ 1) → x ∈ X)
    (hU : ∀ u, (∀ row, inputRow row u ≤ 1) → u ∈ U)
    (hrows : ∀ x ∈ terminal,
      (∀ row, stateRow row x ≤ 1-epsilon N) ∧
      (∀ row, inputRow row (control x) ≤ 1-epsilon N)) :
    terminal ⊆ X ∧ ∀ x ∈ terminal, control x ∈ U := by
  have hbound : 1-epsilon N ≤ 1 := by linarith
  constructor
  · intro x hx
    exact hX x (fun row => ((hrows x hx).1 row).trans hbound)
  · intro x hx
    exact hU (control x) (fun row => ((hrows x hx).2 row).trans hbound)

/-- The actual printed terminal sublevel is closed. Compactness follows from
its derived inclusion in the compact original state set, without supplying
an attained optimizer, terminal compactness, or an upper coercivity conclusion
as a premise. -/
theorem actual_continuous_terminal_sublevel_and_derived_state_rows_are_compact
    {S : Type*} [TopologicalSpace S]
    (Vf : S → ℝ) (alpha : ℝ) (X : Set S)
    (hVf : Continuous Vf) (hcompactX : IsCompact X)
    (hsubset : {x | Vf x ≤ alpha} ⊆ X) :
    IsClosed {x | Vf x ≤ alpha} ∧ IsCompact {x | Vf x ≤ alpha} := by
  have hclosed : IsClosed {x | Vf x ≤ alpha} := isClosed_le hVf continuous_const
  exact ⟨hclosed,hcompactX.of_isClosed_subset hclosed hsubset⟩

/-- Physical positive-horizon feasible states really satisfy the untightened
state rows: stage zero is included and its epsilon is exactly zero. -/
theorem actual_original_positive_horizon_feasibility_implies_state_constraints
    {S A J K : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (N : ℕ) (hN : 0 < N) (f : S → A → S)
    (stateRow : J → S →L[ℝ] ℝ) (inputRow : K → A →L[ℝ] ℝ)
    (epsilon : ℕ → ℝ) (terminal X : Set S) (hepsilon : epsilon 0=0)
    (hX : ∀ x, (∀ row, stateRow row x ≤ 1) → x ∈ X) :
    {x | (originalFeasiblePlans N x f stateRow inputRow epsilon terminal).Nonempty} ⊆ X := by
  intro x hx
  obtain ⟨p,hp⟩ := hx
  apply hX x
  intro row
  have hs := hp.2.2.1 (⟨0,hN⟩ : Fin N) row
  have hi := hp.1
  simpa [hepsilon,hi] using hs

/-- The selected actual trajectory result gives feasible-state safety;
this direct projection replaces that abstract feasible domain by the actual
source state set once its row-derived inclusion has been proved. -/
theorem actual_safe_convergent_feasible_trajectory_implies_original_state_safety
    {S A : Type*} [NormedAddCommGroup S]
    (f : S × A → S) (approx control : S → A)
    (feasible terminal X : Set S) (U : Set A) (hsubset : feasible ⊆ X)
    (initial : S)
    (houtcome : initial ∈ actualSafeConvergentInitialStates
      f approx control feasible terminal U) :
    (∀ t, trajectory f (switchedFeedback terminal approx control) t initial ∈ X ∧
      switchedFeedback terminal approx control
        (trajectory f (switchedFeedback terminal approx control) t initial) ∈ U) ∧
      Tendsto (fun t => trajectory f (switchedFeedback terminal approx control) t initial)
        atTop (𝓝 0) := by
  exact ⟨fun t => ⟨hsubset (houtcome.1 t).1,(houtcome.1 t).2⟩,houtcome.2⟩

end SafeLearning.CompleteCoreMPCOriginalDomainAndSublevel28


namespace SafeLearning.CompleteCoreMPCInfinityInputCost28
open SafeLearning.CompleteCoreMPCFiniteEntrySwitch26

/-- The physical input has the infinity norm used by the feedback certificate.
Its cost uses the same coordinates in the source Euclidean quadratic form,
exactly as in the selected terminal matrix convergence theorem. -/
def actualInputQuadratic {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin m → ℝ) : ℝ :=
  matrixQuadraticStorage R (WithLp.toLp 2 u)

theorem actual_input_cost_preserves_every_physical_coordinate
    {m : ℕ} (u : Fin m → ℝ) (i : Fin m) :
    (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m)) i = u i := by
  rfl

theorem actual_infinity_input_matrix_quadratic_is_continuous
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (actualInputQuadratic R) := by
  exact (actual_matrix_quadratic_storage_is_continuous R).comp
    (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin m => ℝ))

theorem actual_Q_R_stage_and_P_terminal_costs_are_continuous_in_the_physical_spaces
    {n m : ℕ} (Q P : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) × (Fin m → ℝ) =>
      matrixQuadraticStorage Q z.1 + actualInputQuadratic R z.2) ∧
    Continuous (matrixQuadraticStorage P) := by
  exact ⟨((actual_matrix_quadratic_storage_is_continuous Q).comp continuous_fst).add
    ((actual_infinity_input_matrix_quadratic_is_continuous R).comp continuous_snd),
    actual_matrix_quadratic_storage_is_continuous P⟩

theorem actual_positive_definite_input_matrix_has_nonnegative_physical_cost
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (u : Fin m → ℝ) : 0 ≤ actualInputQuadratic R u := by
  exact actual_positive_definite_matrix_has_nonnegative_quadratic_storage R hR _

end SafeLearning.CompleteCoreMPCInfinityInputCost28

namespace SafeLearning.CompleteCoreMPCPrimaryComposition28
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
open SafeLearning.CompleteCoreMPCTypedDomainShift28
open SafeLearning.CompleteCoreMPCLocalGeometry28
open SafeLearning.CompleteCoreMPCActualMatrixRows28
open SafeLearning.CompleteCoreMPCExactTightening28
open SafeLearning.CompleteCoreMPCFiniteOptimizer28
open SafeLearning.CompleteCoreMPCGlobalOptimizerCertificate28
open SafeLearning.CompleteCoreMPCTerminalPredictionFeasibility28
open SafeLearning.CompleteCoreMPCOriginalDomainAndSublevel28
open SafeLearning.CompleteCoreMPCInfinityInputCost28
open SafeLearning.CompleteCoreMPCOriginalFeedbackNorm28
open SafeLearning.CompleteCoreMPCFiniteEntrySwitch26
open SafeLearning.CompleteLyapunovTrajectoryValidation

abbrev PhysicalState (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev PhysicalInput (m : ℕ) := Fin m → ℝ

def exactSourceEpsilon {n m r s : ℕ}
    (H : Matrix (Fin r) (Fin n) ℝ) (Lt : Matrix (Fin s) (Fin m) ℝ)
    (lambda eta cU cL k rho : ℝ) : ℕ → ℝ :=
  originalTightening (lambda*eta*Real.sqrt (cU/cL)*max ‖H‖ (‖Lt‖*k)) rho

def exactTerminalSublevel {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (alpha : ℝ) : Set (PhysicalState n) := {x | matrixQuadraticStorage P x ≤ alpha}

/-- These are the actual primitive finite-horizon MPC/model assumptions. In
particular no robust-one-step certificate, shifted feasible plan, terminal
feasibility, optimizer, all-time safety or convergence is a field. The
incremental field is the explicitly adopted Source56 partial-domain reading.
The feasible-controller statement uses a positive physical prediction horizon.
State dimension zero remains permitted and is handled directly below. -/
structure PrimaryMPCIngredients (n m r s : ℕ) where
  H : Matrix (Fin r) (Fin n) ℝ
  Lt : Matrix (Fin s) (Fin m) ℝ
  X : Set (PhysicalState n)
  U : Set (PhysicalInput m)
  f : PhysicalState n → PhysicalInput m → PhysicalState n
  tracking : PhysicalState n → PhysicalState n → PhysicalInput m → PhysicalInput m
  V : PhysicalState n → PhysicalState n → PhysicalInput m → ℝ
  cL : ℝ
  delta : ℝ
  k : ℝ
  rho : ℝ
  cU : ℝ
  lambda : ℝ
  eta : ℝ
  cL_pos : 0 < cL
  delta_pos : 0 < delta
  k_pos : 0 < k
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  incremental_lower : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    V x z v ≤ delta → cL * ‖x-z‖^2 ≤ V x z v
  feedback_euclidean : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    V x z v ≤ delta → ‖WithLp.toLp 2 (tracking x z v-v)‖ ≤ k * ‖x-z‖
  successor_domain_and_contraction : ∀ x ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    ∀ vnext ∈ U, f z v ∈ X → V x z v ≤ delta →
      f x (tracking x z v) ∈ X ∧
      V (f x (tracking x z v)) (f z v) vnext ≤ rho * V x z v
  cU_pos : 0 < cU
  lambda_pos : 0 < lambda
  eta_nonneg : 0 ≤ eta
  small_disturbance : eta ≤ lambda⁻¹ * Real.sqrt (delta/cU)
  state_rows : ∀ x, x ∈ X ↔ ∀ row, (H *ᵥ (fun i => x i)) row ≤ 1
  eroded_input_rows : ∀ u, (∀ row, (Lt *ᵥ u) row ≤ 1) ↔
    u ∈ actualInputErosion U {d | ‖d‖ ≤ eta}
  input_lipschitz : ∀ x ∈ X, ∀ u ∈ U, ∀ d : PhysicalInput m, u+d ∈ U →
    ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖
  incremental_continuous : ∀ z ∈ X, ∀ v ∈ U, ContinuousOn (fun y => V y z v) X
  incremental_zero : ∀ z ∈ X, ∀ v ∈ U, V z z v=0
  incremental_upper : ∀ y ∈ X, ∀ z ∈ X, ∀ v ∈ U,
    V y z v ≤ delta → V y z v ≤ cU * ‖y-z‖^2
  N : ℕ
  horizon_pos : 0 < N
  P : Matrix (Fin n) (Fin n) ℝ
  Q : Matrix (Fin n) (Fin n) ℝ
  R : Matrix (Fin m) (Fin m) ℝ
  P_pos : P.PosDef
  Q_pos : Q.PosDef
  R_pos : R.PosDef
  alpha : ℝ
  terminalControl : PhysicalState n → PhysicalInput m
  terminal_rows : ∀ x ∈ exactTerminalSublevel P alpha,
    (∀ row, (H *ᵥ (fun i => x i)) row ≤
      1-exactSourceEpsilon H Lt lambda eta cU cL k rho N) ∧
    (∀ row, (Lt *ᵥ terminalControl x) row ≤
      1-exactSourceEpsilon H Lt lambda eta cU cL k rho N)
  terminal_robust : ∀ x ∈ exactTerminalSublevel P alpha, ∀ w : PhysicalState n,
    ‖w‖ ≤ Real.sqrt (rho^N*cU/cL)*lambda*eta →
    f x (terminalControl x)+w ∈ exactTerminalSublevel P alpha
  terminal_drop : ∀ x ∈ exactTerminalSublevel P alpha,
    matrixQuadraticStorage P (f x (terminalControl x)) ≤ matrixQuadraticStorage P x -
      (matrixQuadraticStorage Q x + actualInputQuadratic R (terminalControl x))
  compact_state : IsCompact X
  compact_input : IsCompact U
  continuous_model : Continuous (fun z : PhysicalState n × PhysicalInput m => f z.1 z.2)

/-- The input-infinity certificate is derived from the printed Euclidean
feedback bound, with exactly the original local domain quantifiers. -/
def derivedIncrementalCertificate {n m r s : ℕ}
    (p : PrimaryMPCIngredients n m r s) :
    TypedLocalIncrementalCertificate p.X p.U p.f p.tracking p.V p.cL p.delta p.k p.rho :=
  actual_original_euclidean_feedback_bounds_construct_the_input_infinity_certificate
    p.X p.U p.f p.tracking p.V p.cL p.delta p.k p.rho p.cL_pos p.delta_pos
    p.k_pos.le p.rho_pos.le p.rho_lt_one p.incremental_lower p.feedback_euclidean
    p.successor_domain_and_contraction

def actualOriginalPlans {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s)
    (x : PhysicalState n) : Set (Plan (PhysicalState n) (PhysicalInput m) p.N) :=
  originalFeasiblePlans p.N x p.f (actualStateRow p.H) (actualInputRow p.Lt)
    (exactSourceEpsilon p.H p.Lt p.lambda p.eta p.cU p.cL p.k p.rho)
    (exactTerminalSublevel p.P p.alpha)

def actualOriginalFeasibleStates {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s) :
    Set (PhysicalState n) := {x | (actualOriginalPlans p x).Nonempty}

def actualOriginalObjective {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s) :
    Plan (PhysicalState n) (PhysicalInput m) p.N → ℝ :=
  originalFiniteObjective p.N
    (fun x u => matrixQuadraticStorage p.Q x+actualInputQuadratic p.R u)
    (matrixQuadraticStorage p.P)

def actualOriginalOptimalFirstInput {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s)
    (mpc : PhysicalState n → PhysicalInput m) : Prop :=
  ∀ x ∈ actualOriginalFeasibleStates p,
    ∃ plan ∈ actualOriginalPlans p x,
      mpc x = plan.2 ⟨0,p.horizon_pos⟩ ∧
      ∀ other ∈ actualOriginalPlans p x,
        actualOriginalObjective p plan ≤ actualOriginalObjective p other

/-- Every terminal/domain interface required by the actual switched-trajectory
result follows from primitive source terminal rows and robust invariance. The
continuous terminal quadratic supplies closedness for the optimizer problem. -/
theorem actual_primary_terminal_ingredients_derive_all_original_domain_interfaces
    {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s) :
    IsClosed (exactTerminalSublevel p.P p.alpha) ∧
    exactTerminalSublevel p.P p.alpha ⊆ p.X ∧
    (∀ x ∈ exactTerminalSublevel p.P p.alpha, p.terminalControl x ∈ p.U) ∧
    (∀ x ∈ exactTerminalSublevel p.P p.alpha,
      p.f x (p.terminalControl x) ∈ exactTerminalSublevel p.P p.alpha) ∧
    exactTerminalSublevel p.P p.alpha ⊆ actualOriginalFeasibleStates p ∧
    actualOriginalFeasibleStates p ⊆ p.X := by
  let epsilon := exactSourceEpsilon p.H p.Lt p.lambda p.eta p.cU p.cL p.k p.rho
  have heps := actual_source_epsilon_is_nonnegative_and_monotone
    p.H p.Lt p.lambda p.eta p.cU p.cL p.k p.rho p.lambda_pos.le p.eta_nonneg
  have hU : ∀ u, (∀ row, actualInputRow p.Lt row u ≤ 1) → u ∈ p.U := by
    intro u hu
    exact (actual_eroded_input_and_bounded_error_are_both_admissible
      p.U p.eta p.eta_nonneg u 0 ((p.eroded_input_rows u).mp hu)
      (by simpa using p.eta_nonneg)).1
  have hdomain := actual_terminal_tightened_rows_derive_original_X_and_U_membership
    (actualStateRow p.H) (actualInputRow p.Lt) p.X
    (exactTerminalSublevel p.P p.alpha) p.U p.terminalControl epsilon p.N
    (heps.1 p.N) (fun x hx => (p.state_rows x).mpr hx) hU p.terminal_rows
  have hradius : 0 ≤ Real.sqrt (p.rho^p.N*p.cU/p.cL)*p.lambda*p.eta :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) p.lambda_pos.le) p.eta_nonneg
  have hinvariant := actual_robust_terminal_ingredient_contains_the_zero_disturbance_case
    (fun z => p.f z.1 z.2) p.terminalControl (exactTerminalSublevel p.P p.alpha)
    (Real.sqrt (p.rho^p.N*p.cU/p.cL)*p.lambda*p.eta) hradius p.terminal_robust
  have hterminal := actual_terminal_ingredients_derive_original_mpc_feasibility
    p.f p.terminalControl (actualStateRow p.H) (actualInputRow p.Lt) epsilon
    (exactTerminalSublevel p.P p.alpha) p.N hinvariant p.terminal_rows
    (fun j hj => heps.2 hj.le)
  have hfeasible := actual_original_positive_horizon_feasibility_implies_state_constraints
    p.N p.horizon_pos p.f (actualStateRow p.H) (actualInputRow p.Lt) epsilon
    (exactTerminalSublevel p.P p.alpha) p.X (by rfl)
    (fun x hx => (p.state_rows x).mpr hx)
  have hclosed : IsClosed (exactTerminalSublevel p.P p.alpha) :=
    isClosed_le (actual_matrix_quadratic_storage_is_continuous p.P) continuous_const
  exact ⟨hclosed,hdomain.1,hdomain.2,hinvariant,hterminal,hfeasible⟩

/-- Actual compactness/continuity yields an original globally optimal MPC
policy; the independent bootstrap then derives its robust certificate. No
optimizer or desired next-feasibility conclusion is assumed. -/
theorem actual_primary_mpc_ingredients_have_an_optimal_recursively_feasible_controller
    {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s) :
    ∃ mpc, actualOriginalOptimalFirstInput p mpc ∧
      robustOneStepCertificate (fun z => p.f z.1 z.2) mpc
        (actualOriginalFeasibleStates p) p.U p.eta := by
  obtain ⟨hclosed,htermX,htermU,hinvariant,htermFeas,hfeasX⟩ :=
    actual_primary_terminal_ingredients_derive_all_original_domain_interfaces p
  have heps := actual_source_epsilon_is_nonnegative_and_monotone
    p.H p.Lt p.lambda p.eta p.cU p.cL p.k p.rho p.lambda_pos.le p.eta_nonneg
  have hU : ∀ u, (∀ row, actualInputRow p.Lt row u ≤ 1) → u ∈ p.U := by
    intro u hu
    exact (actual_eroded_input_and_bounded_error_are_both_admissible
      p.U p.eta p.eta_nonneg u 0 ((p.eroded_input_rows u).mp hu)
      (by simpa using p.eta_nonneg)).1
  obtain ⟨mpc,hoptimal⟩ := actual_attained_original_optimizers_supply_a_total_first_input_policy
    p.N p.horizon_pos p.f (actualStateRow p.H) (actualInputRow p.Lt)
    (exactSourceEpsilon p.H p.Lt p.lambda p.eta p.cU p.cL p.k p.rho)
    (exactTerminalSublevel p.P p.alpha) p.X p.U p.state_rows hU (fun j => heps.1 j)
    htermX p.compact_state p.compact_input p.continuous_model hclosed
    (fun x u => matrixQuadraticStorage p.Q x+actualInputQuadratic p.R u)
    (matrixQuadraticStorage p.P)
    (actual_Q_R_stage_and_P_terminal_costs_are_continuous_in_the_physical_spaces p.Q p.P p.R).1
    (actual_Q_R_stage_and_P_terminal_costs_are_continuous_in_the_physical_spaces p.Q p.P p.R).2
  refine ⟨mpc,hoptimal,?_⟩
  apply actual_original_prediction_choice_derives_the_robust_one_step_certificate
    p.H p.Lt p.X p.U p.f p.tracking p.V p.cL p.delta p.k p.rho p.cU p.lambda p.eta
    (derivedIncrementalCertificate p) p.cU_pos p.lambda_pos p.eta_nonneg p.small_disturbance p.state_rows
    p.eroded_input_rows p.input_lipschitz p.incremental_continuous p.incremental_zero
    p.incremental_upper (exactTerminalSublevel p.P p.alpha) p.terminalControl p.N p.horizon_pos
    p.terminal_rows p.terminal_robust mpc
  intro x hx
  obtain ⟨plan,hplan,hfirst,hmin⟩ := hoptimal x hx
  exact ⟨plan,hplan,hfirst⟩

/-- The actual source MPC ingredients and a truly attained original optimizer
are sufficient for all-time original state/input safety and convergence on
the finite-entry validated event. State dimension zero is proved directly;
no full safety or terminal-convergence conclusion is a premise. -/
theorem actual_original_optimizer_and_source_ingredients_derive_safe_convergent_hybrid_paths
    {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s)
    (mpc approx : PhysicalState n → PhysicalInput m)
    (hoptimal : actualOriginalOptimalFirstInput p mpc)
    (initial : PhysicalState n) (hinitial : initial ∈ actualOriginalFeasibleStates p)
    (hgood : initial ∈ goodInitialStates (fun z => p.f z.1 z.2) approx mpc
      (exactTerminalSublevel p.P p.alpha) p.eta) :
    initial ∈ actualSafeConvergentInitialStates (fun z => p.f z.1 z.2)
      approx p.terminalControl p.X (exactTerminalSublevel p.P p.alpha) p.U := by
  obtain ⟨hclosed,htermX,htermU,hinvariant,htermFeas,hfeasX⟩ :=
    actual_primary_terminal_ingredients_derive_all_original_domain_interfaces p
  have hrobust : robustOneStepCertificate (fun z => p.f z.1 z.2) mpc
      (actualOriginalFeasibleStates p) p.U p.eta := by
    apply actual_original_prediction_choice_derives_the_robust_one_step_certificate
      p.H p.Lt p.X p.U p.f p.tracking p.V p.cL p.delta p.k p.rho p.cU p.lambda p.eta
      (derivedIncrementalCertificate p) p.cU_pos p.lambda_pos p.eta_nonneg p.small_disturbance p.state_rows
      p.eroded_input_rows p.input_lipschitz p.incremental_continuous p.incremental_zero
      p.incremental_upper (exactTerminalSublevel p.P p.alpha) p.terminalControl p.N p.horizon_pos
      p.terminal_rows p.terminal_robust mpc
    intro x hx
    obtain ⟨plan,hplan,hfirst,hmin⟩ := hoptimal x hx
    exact ⟨plan,hplan,hfirst⟩
  have hsafety := actual_good_finite_entry_initial_state_has_all_time_hybrid_state_and_input_safety
    (fun z => p.f z.1 z.2) approx mpc p.terminalControl
    (actualOriginalFeasibleStates p) (exactTerminalSublevel p.P p.alpha) p.U p.eta
    hrobust htermFeas hinvariant htermU initial hinitial hgood
  refine ⟨fun t => ⟨hfeasX (hsafety t).1,(hsafety t).2⟩,?_⟩
  by_cases hn : n=0
  · subst n
    have heq : (fun t => trajectory (fun z => p.f z.1 z.2)
        (switchedFeedback (exactTerminalSublevel p.P p.alpha) approx p.terminalControl)
        t initial) = fun _ => (0 : PhysicalState 0) := by
      funext t
      exact Subsingleton.elim _ _
    rw [heq]
    exact tendsto_const_nhds
  · letI : Nonempty (Fin n) := ⟨⟨0,Nat.pos_of_ne_zero hn⟩⟩
    exact (actual_checked_finite_entry_and_terminal_matrices_imply_the_true_safe_convergent_hybrid_event
      (fun z => p.f z.1 z.2) approx mpc p.terminalControl (actualOriginalFeasibleStates p)
      (exactTerminalSublevel p.P p.alpha) p.U p.eta hrobust htermFeas hinvariant htermU
      p.P p.Q p.R p.P_pos p.Q_pos p.R_pos p.terminal_drop initial hinitial hgood).2

/-- The probability comparison concerns the same physical initial law and
actual switched paths. It is derived from the original MPC certificate,
not supplied as an initial probability-of-safety premise. -/
theorem actual_original_mpc_and_initial_law_transfer_finite_entry_probability_to_safe_convergence
    {n m r s : ℕ} (p : PrimaryMPCIngredients n m r s)
    (mu : Measure (PhysicalState n))
    (mpc approx : PhysicalState n → PhysicalInput m)
    (hoptimal : actualOriginalOptimalFirstInput p mpc)
    (hfeasible : ∀ᵐ initial ∂mu, initial ∈ actualOriginalFeasibleStates p) :
    mu (goodInitialStates (fun z => p.f z.1 z.2) approx mpc
      (exactTerminalSublevel p.P p.alpha) p.eta) ≤
    mu (actualSafeConvergentInitialStates (fun z => p.f z.1 z.2) approx p.terminalControl
      p.X (exactTerminalSublevel p.P p.alpha) p.U) := by
  apply measure_mono_ae
  filter_upwards [hfeasible] with initial hinitial
  exact actual_original_optimizer_and_source_ingredients_derive_safe_convergent_hybrid_paths
    p mpc approx hoptimal initial hinitial

end SafeLearning.CompleteCoreMPCPrimaryComposition28
