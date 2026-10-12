import SafeLearning.CompleteModulesChowTermination21
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SafeLearning.CompleteModulesChowAbsorption21
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteControlledPathFlow
open SafeLearning.CompleteModulesChowVisitCost21
open SafeLearning.CompleteModulesChowControlled21
open SafeLearning.CompleteModulesChowTermination21
local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => MeasurableSet.of_discrete⟩

def firstAbsorptionTime (path : ℕ → Fin 4 × Bool) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, (path n).1=3 then Nat.find h else 0

theorem actual_terminal_to_nonterminal_one_step_event_has_zero_probability
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (j : Fin 3) :
    (law π).real {path | (path n).1=3 ∧ (path (n+1)).1=j.castSucc}=0 := by
  have hp := actual_finite_event_partition (law π) (fun path => (path n).2)
    {path | (path n).1=3 ∧ (path (n+1)).1=j.castSucc}
    (fun a : Bool => by
      have hs : MeasurableSet {path : ℕ → Fin 4 × Bool | (path n).1=3} := (measurableSet_singleton (3 : Fin 4)).preimage
        (measurable_fst.comp (measurable_pi_apply n))
      have ha : MeasurableSet {path : ℕ → Fin 4 × Bool | (path n).2=a} := (measurableSet_singleton a).preimage
        (measurable_snd.comp (measurable_pi_apply n))
      have ht : MeasurableSet {path : ℕ → Fin 4 × Bool | (path (n+1)).1=j.castSucc} := (measurableSet_singleton j.castSucc).preimage
        (measurable_fst.comp (measurable_pi_apply (n+1)))
      simpa only [Set.inter_def,Set.mem_ofPred_eq] using ha.inter (hs.inter ht))
  rw [hp]
  apply Finset.sum_eq_zero
  intro a _
  have h := actual_constructed_path_has_the_controlled_transition_law model π n 3 a j.castSucc
  cases a <;> fin_cases j <;>
    simpa [law,model,fullKernel,and_assoc,and_comm,and_left_comm] using h

theorem actual_absorbing_state_remains_absorbing_almost_surely_for_every_policy
    (π : HistoryPolicy (Fin 4) Bool) :
    ∀ᵐ path ∂law π, ∀ n : ℕ, (path n).1=3 → (path (n+1)).1=3 := by
  have hbad (n : ℕ) (j : Fin 3) :
      ∀ᵐ path ∂law π, ¬((path n).1=3 ∧ (path (n+1)).1=j.castSucc) := by
    have hz := (measureReal_eq_zero_iff).mp
      (actual_terminal_to_nonterminal_one_step_event_has_zero_probability π n j)
    exact measure_eq_zero_iff_ae_notMem.mp hz
  have hh : ∀ᵐ path ∂law π, ∀ n : ℕ, ∀ j : Fin 3,
      ¬((path n).1=3 ∧ (path (n+1)).1=j.castSucc) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hbad n))
  filter_upwards [hh] with path hp
  intro n hn
  have h0 := hp n 0
  have h1 := hp n 1
  have h2 := hp n 2
  generalize hx : (path (n+1)).1=s at *
  fin_cases s <;> norm_num at * <;> contradiction

theorem actual_transient_visit_count_equals_first_absorption_time
    (path : ℕ → Fin 4 × Bool)
    (hex : ∃ n : ℕ, (path n).1=3)
    (habs : ∀ n : ℕ, (path n).1=3 → (path (n+1)).1=3) :
    totalVisits path=(firstAbsorptionTime path : ℝ) := by
  let T := Nat.find hex
  have hT : (path T).1=3 := Nat.find_spec hex
  have hafter : ∀ n : ℕ, T≤n → (path n).1=3 := by
    intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simpa using hT
    | succ k ih => simpa [Nat.add_assoc] using habs (T+k) (ih (by omega))
  have hbefore : ∀ n : ℕ, n<T → (path n).1≠3 := fun n hn => Nat.find_min hex hn
  have hvisit (j : Fin 3) : visits j path=
      ∑ n ∈ Finset.range T, (visitEvents j n).indicator (fun _ => (1:ℝ)) path := by
    unfold visits realVisits
    apply tsum_eq_sum
    intro n hn
    have hnt : T≤n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    have hnj : path∉visitEvents j n := by
      change (path n).1≠j.castSucc
      rw [hafter n hnt]
      fin_cases j <;> norm_num
    simp [Set.indicator,hnj]
  unfold totalVisits
  simp_rw [hvisit]
  rw [Finset.sum_comm]
  have hterm (n : ℕ) (hn : n∈Finset.range T) :
      (∑ j : Fin 3, (visitEvents j n).indicator (fun _ => (1:ℝ)) path)=1 := by
    have hnt := hbefore n (Finset.mem_range.mp hn)
    simp only [Fin.sum_univ_succ]
    generalize hx : (path n).1=s at *
    fin_cases s <;> norm_num [visitEvents,Set.indicator,hx] at *
  rw [Finset.sum_congr rfl hterm]
  simp [firstAbsorptionTime,hex,T]

theorem actual_every_policy_has_integrable_first_absorption_time_and_literal_expected_duration
    (π : HistoryPolicy (Fin 4) Bool) :
    Integrable (fun path => (firstAbsorptionTime path : ℝ)) (law π) ∧
      (∫ path, (firstAbsorptionTime path : ℝ) ∂law π)=(213-28*initialMix π)/95 := by
  have he := actual_every_history_policy_terminates_almost_surely π
  have ha := actual_absorbing_state_remains_absorbing_almost_surely_for_every_policy π
  have hEq : totalVisits=ᵐ[law π] (fun path => (firstAbsorptionTime path : ℝ)) := by
    filter_upwards [he,ha] with path hp habs
    obtain ⟨N,hN⟩ := hp
    exact actual_transient_visit_count_equals_first_absorption_time path ⟨N,hN N le_rfl⟩ habs
  have h := actual_total_transient_visits_are_integrable_and_have_the_true_expectation π
  exact ⟨h.1.congr hEq,(integral_congr_ae hEq).symm.trans h.2⟩

end SafeLearning.CompleteModulesChowAbsorption21
