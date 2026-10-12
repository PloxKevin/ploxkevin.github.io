import SafeLearning.CompleteCoreMPCFirstSuccessor27
import Mathlib.Topology.Order.Compact

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
