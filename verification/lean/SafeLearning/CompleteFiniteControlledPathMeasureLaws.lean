import SafeLearning.CompleteFiniteControlledPathMeasure

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SafeLearning.CompleteFiniteControlledPathMeasureLaws

open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure

variable {S A : Type*} [Fintype S] [Fintype A]
variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

theorem actual_initial_history_distribution (M : Model S A) (π : HistoryPolicy S A) :
    (controlledPathMeasure M π).map (Preorder.frestrictLe 0) =
      (initialPMF M π).toMeasure.map (MeasurableEquiv.piUnique _).symm := by
  unfold controlledPathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp]

theorem actual_initial_joint_distribution (M : Model S A) (π : HistoryPolicy S A) :
    (controlledPathMeasure M π).map (fun path => path 0) = (initialPMF M π).toMeasure := by
  have hf : (fun path : ℕ → S × A => path 0) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S × A)) ∘ Preorder.frestrictLe 0 := by
    funext path
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    actual_initial_history_distribution, Measure.map_map (by fun_prop) (by fun_prop)]
  change (initialPMF M π).toMeasure.map id = (initialPMF M π).toMeasure
  exact Measure.map_id

theorem actual_initial_joint_event_probability (M : Model S A) (π : HistoryPolicy S A)
    (z : S × A) :
    (controlledPathMeasure M π).real {path | path 0 = z} = initialJoint M π z := by
  have he := congrArg (fun ν : Measure (S × A) => ν.real {z})
    (actual_initial_joint_distribution M π)
  change (((controlledPathMeasure M π).map (fun path => path 0)) {z}).toReal =
    ((initialPMF M π).toMeasure {z}).toReal at he
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)] at he
  change (controlledPathMeasure M π).real {path | path 0 = z} =
    ((initialPMF M π).toMeasure {z}).toReal at he
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  exact ENNReal.toReal_ofReal (actual_initial_joint_nonnegative M π z)

theorem actual_history_kernel_next_state_probability (M : Model S A)
    (π : HistoryPolicy S A) (n : ℕ) (history : (i : Finset.Iic n) → S × A) (t : S) :
    (historyKernel M π n history).real {z | z.1 = t} =
      M.transition (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1
        (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 t := by
  classical
  change ((stepPMF M π n history).toMeasure {z | z.1 = t}).toReal = _
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun z _ => by
    by_cases hz : z.1 = t <;> simp [Set.indicator, hz, stepPMF])]
  simp only [stepPMF, PMF.ofFintype_apply]
  change (∑ z : S × A, (Set.indicator {z | z.1 = t}
      (fun z => ENNReal.ofReal (stepJoint M π n history z)) z).toReal) = _
  have hc : (∑ z : S × A, (Set.indicator {z | z.1 = t}
      (fun z => ENNReal.ofReal (stepJoint M π n history z)) z).toReal) =
      ∑ z : S × A, if z.1 = t then stepJoint M π n history z else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z.1 = t
    · simp only [Set.indicator, Set.mem_ofPred_eq, hz, ite_true]
      exact ENNReal.toReal_ofReal (actual_step_joint_nonnegative M π n history z)
    · simp [Set.indicator, hz]
  rw [hc, Fintype.sum_prod_type]
  have hs : (∑ s, ∑ a, if s = t then stepJoint M π n history (s, a) else 0) =
      ∑ s, if s = t then (∑ a, stepJoint M π n history (s, a)) else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hst : s = t <;> simp [hst]
  rw [hs]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [stepJoint, ← Finset.mul_sum, π.action_sum, mul_one]

theorem actual_constructed_path_has_the_controlled_transition_law
    (M : Model S A) (π : HistoryPolicy S A) (n : ℕ) (s : S) (a : A) (t : S) :
    (controlledPathMeasure M π).real
        {path | (path n).1 = s ∧ (path n).2 = a ∧ (path (n + 1)).1 = t} =
      (controlledPathMeasure M π).real {path | (path n).1 = s ∧ (path n).2 = a} *
        M.transition s a t := by
  let E : Set ((i : Finset.Iic n) → S × A) :=
    {history | history ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = (s, a)}
  let T : Set (S × A) := {z | z.1 = t}
  let ν := (controlledPathMeasure M π).map (Preorder.frestrictLe n)
  have hE : MeasurableSet E :=
    (measurableSet_singleton (s, a)).preimage (measurable_pi_apply _)
  have hT : MeasurableSet T := (measurableSet_singleton t).preimage measurable_fst
  have hκ : ∀ history ∈ E, historyKernel M π n history T = ENNReal.ofReal (M.transition s a t) := by
    intro history hh
    change history ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = (s, a) at hh
    calc
      _ = ENNReal.ofReal ((historyKernel M π n history).real T) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (M.transition
          (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1
          (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 t) :=
        congrArg ENNReal.ofReal (actual_history_kernel_next_state_probability M π n history t)
      _ = _ := by rw [hh]
  have hcp : (ν ⊗ₘ historyKernel M π n).real (E ×ˢ T) =
      ν.real E * M.transition s a t := by
    change ((ν ⊗ₘ historyKernel M π n) (E ×ˢ T)).toReal = _
    rw [Measure.compProd_apply_prod hE hT,
      setLIntegral_congr_fun hE hκ, setLIntegral_const,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (M.transition_nonneg s a t)]
    simp only [measureReal_def]
    ring
  have hjoint : (ν ⊗ₘ historyKernel M π n) (E ×ˢ T) =
      (controlledPathMeasure M π) {path | path n = (s, a) ∧ (path (n + 1)).1 = t} := by
    rw [actual_full_history_successor_joint_law M π n,
      Measure.map_apply (by fun_prop) (hE.prod hT)]
    rfl
  have hcurrent : ν E = (controlledPathMeasure M π) {path | path n = (s, a)} := by
    exact Measure.map_apply (by fun_prop) hE
  change ((ν ⊗ₘ historyKernel M π n) (E ×ˢ T)).toReal =
    (ν E).toReal * M.transition s a t at hcp
  rw [hjoint, hcurrent] at hcp
  simpa only [measureReal_def, Prod.ext_iff, and_assoc] using hcp

theorem actual_constructed_path_initial_state_law (M : Model S A)
    (π : HistoryPolicy S A) (s : S) :
    (controlledPathMeasure M π).real {path | (path 0).1 = s} = M.initial s := by
  have h0 : Measurable (fun path : ℕ → S × A => path 0) := measurable_pi_apply 0
  have hp := SafeLearning.CompleteFiniteControlledPathFlow.actual_finite_event_partition
    (controlledPathMeasure M π) (fun path => (path 0).2) {path | (path 0).1 = s}
    (fun a => by
      have hs := (measurableSet_singleton s).preimage h0.fst
      have ha := (measurableSet_singleton a).preimage h0.snd
      simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage,
        Set.mem_singleton_iff] using ha.inter hs)
  have hj : ∀ a, (controlledPathMeasure M π).real
      {path | (path 0).2 = a ∧ path ∈ {path | (path 0).1 = s}} = initialJoint M π (s, a) := by
    intro a
    simpa only [Set.mem_ofPred_eq, Prod.ext_iff, and_comm] using
      actual_initial_joint_event_probability M π (s, a)
  simp_rw [hj] at hp
  rw [hp]
  simp only [initialJoint, ← Finset.mul_sum, π.action_sum, mul_one]

theorem actual_constructed_history_path_controlled_law (M : Model S A)
    (π : HistoryPolicy S A) :
    SafeLearning.CompleteFiniteControlledPathFlow.ControlledLaw M
      (controlledPathMeasure M π) (fun n path => (path n).1) (fun n path => (path n).2) := by
  have hm (n : ℕ) : Measurable (fun path : ℕ → S × A => path n) := measurable_pi_apply n
  constructor
  · intro n s
    exact (measurableSet_singleton s).preimage (hm n).fst
  · intro n s a
    have hs := (measurableSet_singleton s).preimage (hm n).fst
    have ha := (measurableSet_singleton a).preimage (hm n).snd
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff] using hs.inter ha
  · exact actual_constructed_path_initial_state_law M π
  · exact actual_constructed_path_has_the_controlled_transition_law M π

theorem actual_all_history_policies_have_flow_feasible_path_occupancy
    (M : Model S A) (π : HistoryPolicy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    SafeLearning.CompleteFiniteCMDPFlow.FlowFeasible M γ
      (SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M π) (fun n path => (path n).1)
        (fun n path => (path n).2) γ) :=
  SafeLearning.CompleteFiniteControlledPathFlow.actual_every_controlled_history_law_satisfies_bellman_flow
    (controlledPathMeasure M π) M (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law M π) γ hγ0 hγ1

theorem actual_all_history_policies_have_the_true_path_return_formula
    (M : Model S A) (π : HistoryPolicy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S → A → ℝ) :
    (∫ path, ∑' n : ℕ, γ ^ n * r (path n).1 (path n).2 ∂controlledPathMeasure M π) =
      (∑ s, ∑ a, SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M π) (fun n path => (path n).1)
        (fun n path => (path n).2) γ s a * r s a) / (1 - γ) :=
  SafeLearning.CompleteFiniteControlledPathFlow.actual_every_controlled_history_law_return_formula
    (controlledPathMeasure M π) M (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law M π) γ hγ0 hγ1 r

theorem actual_all_history_path_occupancies_are_realized_by_stationary_finite_policies
    (M : Model S A) (π : HistoryPolicy S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ σ : Policy S A, (∀ n s a, σ.action n s a = σ.action 0 s a) ∧
      occupancy M σ γ = SafeLearning.CompleteFiniteControlledPathFlow.controlledOccupancy
        (controlledPathMeasure M π) (fun n path => (path n).1)
        (fun n path => (path n).2) γ := by
  obtain ⟨z, _⟩ := (initialPMF M π).support_nonempty
  exact SafeLearning.CompleteFiniteControlledPathFlow.actual_history_path_occupancy_is_realized_by_a_stationary_policy
    (controlledPathMeasure M π) M (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law M π) z.2 γ hγ0 hγ1

end SafeLearning.CompleteFiniteControlledPathMeasureLaws
