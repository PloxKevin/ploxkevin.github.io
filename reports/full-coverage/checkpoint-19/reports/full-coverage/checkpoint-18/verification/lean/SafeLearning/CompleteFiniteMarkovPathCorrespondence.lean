import SafeLearning.CompleteFiniteControlledPathMeasureLaws

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SafeLearning.CompleteFiniteMarkovPathCorrespondence

open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws

variable {S A : Type*} [Fintype S] [Fintype A]
variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- A randomized Markov policy is a genuine nonanticipative history policy. -/
def markovHistoryPolicy (π : Policy S A) : HistoryPolicy S A where
  action n _ s a := π.action n s a
  action_nonneg n _ s a := π.action_nonneg n s a
  action_sum n _ s := π.action_sum n s

theorem actual_markov_path_pair_transition_event (M : Model S A) (π : Policy S A)
    (n : ℕ) (z w : S × A) :
    (controlledPathMeasure M (markovHistoryPolicy π)).real
        {path | path n = z ∧ path (n + 1) = w} =
      (controlledPathMeasure M (markovHistoryPolicy π)).real {path | path n = z} *
        (M.transition z.1 z.2 w.1 * π.action (n + 1) w.1 w.2) := by
  let E : Set ((i : Finset.Iic n) → S × A) :=
    {history | history ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = z}
  let ν := (controlledPathMeasure M (markovHistoryPolicy π)).map (Preorder.frestrictLe n)
  have hE : MeasurableSet E :=
    (measurableSet_singleton z).preimage (measurable_pi_apply _)
  have hκ : ∀ history ∈ E, historyKernel M (markovHistoryPolicy π) n history {w} =
      ENNReal.ofReal (M.transition z.1 z.2 w.1 * π.action (n + 1) w.1 w.2) := by
    intro history hh
    change history ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = z at hh
    calc
      _ = ENNReal.ofReal ((historyKernel M (markovHistoryPolicy π) n history).real {w}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (stepJoint M (markovHistoryPolicy π) n history w) :=
        congrArg ENNReal.ofReal
          (actual_history_kernel_singleton_probability M (markovHistoryPolicy π) n history w)
      _ = _ := by simp only [stepJoint, markovHistoryPolicy, hh]
  have hcp : (ν ⊗ₘ historyKernel M (markovHistoryPolicy π) n).real (E ×ˢ {w}) =
      ν.real E * (M.transition z.1 z.2 w.1 * π.action (n + 1) w.1 w.2) := by
    change ((ν ⊗ₘ historyKernel M (markovHistoryPolicy π) n) (E ×ˢ {w})).toReal = _
    rw [Measure.compProd_apply_prod hE (measurableSet_singleton w),
      setLIntegral_congr_fun hE hκ, setLIntegral_const,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (mul_nonneg (M.transition_nonneg _ _ _) (π.action_nonneg _ _ _))]
    simp only [measureReal_def]
    ring
  have hjoint : (ν ⊗ₘ historyKernel M (markovHistoryPolicy π) n) (E ×ˢ {w}) =
      (controlledPathMeasure M (markovHistoryPolicy π))
        {path | path n = z ∧ path (n + 1) = w} := by
    rw [actual_full_history_successor_joint_law M (markovHistoryPolicy π) n,
      Measure.map_apply (by fun_prop) (hE.prod (measurableSet_singleton w))]
    rfl
  have hcurrent : ν E =
      (controlledPathMeasure M (markovHistoryPolicy π)) {path | path n = z} := by
    exact Measure.map_apply (by fun_prop) hE
  change ((ν ⊗ₘ historyKernel M (markovHistoryPolicy π) n) (E ×ˢ {w})).toReal =
    (ν E).toReal * (M.transition z.1 z.2 w.1 * π.action (n + 1) w.1 w.2) at hcp
  rw [hjoint, hcurrent] at hcp
  exact hcp

theorem actual_markov_path_joint_probability_recurrence (M : Model S A) (π : Policy S A)
    (n : ℕ) (w : S × A) :
    (controlledPathMeasure M (markovHistoryPolicy π)).real {path | path (n + 1) = w} =
      ∑ z : S × A, (controlledPathMeasure M (markovHistoryPolicy π)).real
        {path | path n = z} * (M.transition z.1 z.2 w.1 * π.action (n + 1) w.1 w.2) := by
  have hm (k : ℕ) : Measurable (fun path : ℕ → S × A => path k) := measurable_pi_apply k
  have hp := SafeLearning.CompleteFiniteControlledPathFlow.actual_finite_event_partition
    (controlledPathMeasure M (markovHistoryPolicy π)) (fun path => path n)
    {path | path (n + 1) = w} (fun z => by
      simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage,
        Set.mem_singleton_iff] using
        ((measurableSet_singleton z).preimage (hm n)).inter
          ((measurableSet_singleton w).preimage (hm (n + 1))))
  simpa only [Set.mem_ofPred_eq, actual_markov_path_pair_transition_event] using hp

theorem actual_constructed_markov_path_joint_mass (M : Model S A) (π : Policy S A)
    (n : ℕ) (s : S) (a : A) :
    (controlledPathMeasure M (markovHistoryPolicy π)).real {path | path n = (s, a)} =
      jointMass M π n s a := by
  induction n generalizing s a with
  | zero =>
    simpa only [initialJoint, markovHistoryPolicy, jointMass, stateMass] using
      actual_initial_joint_event_probability M (markovHistoryPolicy π) (s, a)
  | succ n ih =>
    rw [actual_markov_path_joint_probability_recurrence, Fintype.sum_prod_type]
    simp_rw [ih]
    simp only [jointMass, stateMass, Finset.sum_mul, mul_assoc]

theorem actual_constructed_markov_path_occupancy (M : Model S A) (π : Policy S A)
    (γ : ℝ) :
    SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
      (controlledPathMeasure M (markovHistoryPolicy π))
      (fun n path => (path n).1) (fun n path => (path n).2) γ = occupancy M π γ := by
  funext s a
  unfold SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy occupancy
  congr 1
  apply tsum_congr
  intro n
  congr 1
  simpa only [SafeLearning.CompleteFiniteControlledPathFlow.jointProbability, Prod.ext_iff] using
    actual_constructed_markov_path_joint_mass M π n s a

theorem actual_constructed_markov_path_expected_return (M : Model S A) (π : Policy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2
      ∂controlledPathMeasure M (markovHistoryPolicy π)) = expectedReturn M π γ r := by
  rw [actual_all_history_policies_have_the_true_path_return_formula M (markovHistoryPolicy π)
      γ hγ0 hγ1 r, actual_constructed_markov_path_occupancy,
    actual_reward_return_identity M π γ hγ0 hγ1 r]

theorem actual_every_feasible_flow_has_a_constructed_stationary_path
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : SafeLearning.CompleteFiniteCMDPFlow.FlowFeasible M γ ρ) :
    ∃ π : HistoryPolicy S A, (∀ n history s a, π.action n history s a =
        π.action 0 (fun i => Fin.elim0 i) s a) ∧
      SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M π) (fun n path => (path n).1)
        (fun n path => (path n).2) γ = ρ := by
  refine ⟨markovHistoryPolicy
    (SafeLearning.CompleteFiniteCMDPRecovery.recoveredPolicy a₀ ρ hρ.1), ?_, ?_⟩
  · intro n history s a
    rfl
  · rw [actual_constructed_markov_path_occupancy]
    exact SafeLearning.CompleteFiniteCMDPRecovery.actual_every_feasible_flow_is_realized_by_recovered_stationary_policy
      M a₀ γ hγ0 hγ1 ρ hρ

theorem actual_every_history_path_is_matched_by_a_constructed_stationary_path
    (M : Model S A) (π : HistoryPolicy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ σ : HistoryPolicy S A, (∀ n history s a, σ.action n history s a =
        σ.action 0 (fun i => Fin.elim0 i) s a) ∧
      SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M σ) (fun n path => (path n).1) (fun n path => (path n).2) γ =
      SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M π) (fun n path => (path n).1) (fun n path => (path n).2) γ := by
  obtain ⟨z, _⟩ := (initialPMF M π).support_nonempty
  exact actual_every_feasible_flow_has_a_constructed_stationary_path M z.2 γ hγ0 hγ1 _
    (actual_all_history_policies_have_flow_feasible_path_occupancy M π γ hγ0 hγ1)

end SafeLearning.CompleteFiniteMarkovPathCorrespondence
