import SafeLearning.CompleteModulesChowControlled21

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SafeLearning.CompleteModulesChowTermination21
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteModulesChowVisitCost21
open SafeLearning.CompleteModulesChowControlled21
open SafeLearning.CompleteChowLP21
local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => MeasurableSet.of_discrete⟩

def visitEvents (j : Fin 3) (n : ℕ) : Set (ℕ → Fin 4 × Bool) :=
  {path | (path n).1=j.castSucc}

def visits (j : Fin 3) (path : ℕ → Fin 4 × Bool) : ℝ := realVisits (visitEvents j) path

def totalVisits (path : ℕ → Fin 4 × Bool) : ℝ := ∑ j : Fin 3, visits j path

theorem actual_every_history_policy_has_the_true_undiscounted_visit_expectations
    (π : HistoryPolicy (Fin 4) Bool) (j : Fin 3) :
    (∀ᵐ path ∂law π, extendedVisits (visitEvents j) path≠∞) ∧
      Integrable (visits j) (law π) ∧
      (∫ path, visits j path ∂law π)=mixedFundamental (initialMix π) 0 j := by
  have hs := actual_mixed_entry_visit_series (initialMix π) 0 j
  apply actual_summable_visit_probabilities_make_the_undiscounted_count_finite_and_integrable
  · intro n
    exact (measurableSet_singleton j.castSucc).preimage
      (measurable_fst.comp (measurable_pi_apply n))
  · apply hs.congr_fun
    intro n
    change mass π n j.castSucc=(fastTransition (initialMix π)^n) 0 j
    exact actual_every_history_policy_has_the_literal_matrix_power_marginals π n j

theorem actual_finite_undiscounted_visits_imply_an_event_is_eventually_absent
    {Ω : Type*} (events : ℕ → Set Ω) (ω : Ω)
    (hfinite : extendedVisits events ω≠∞) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ω∉events n := by
  have hs := ENNReal.summable_toReal (f:=fun n =>
    (events n).indicator (fun _ => (1:ℝ≥0∞)) ω) hfinite
  have he : (fun n => ((events n).indicator (fun _ => (1:ℝ≥0∞)) ω).toReal)=
      (fun n => (events n).indicator (fun _ => (1:ℝ)) ω) := by
    funext n
    by_cases hn : ω∈events n <;> simp [Set.indicator,hn]
  rw [he] at hs
  have hh : ∀ᶠ n in atTop, (events n).indicator (fun _ => (1:ℝ)) ω<1 :=
    hs.tendsto_atTop_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun n hn hmem => ?_⟩
  have h:=hN n hn
  simp [Set.indicator,hmem] at h

theorem actual_every_history_policy_terminates_almost_surely
    (π : HistoryPolicy (Fin 4) Bool) :
    ∀ᵐ path ∂law π, ∃ N : ℕ, ∀ n : ℕ, N≤n → (path n).1=3 := by
  have hf : ∀ᵐ path ∂law π, ∀ j : Fin 3, extendedVisits (visitEvents j) path≠∞ :=
    ae_all_iff.mpr (fun j => (actual_every_history_policy_has_the_true_undiscounted_visit_expectations π j).1)
  filter_upwards [hf] with path hp
  obtain ⟨N0,h0⟩ := actual_finite_undiscounted_visits_imply_an_event_is_eventually_absent
    (visitEvents 0) path (hp 0)
  obtain ⟨N1,h1⟩ := actual_finite_undiscounted_visits_imply_an_event_is_eventually_absent
    (visitEvents 1) path (hp 1)
  obtain ⟨N2,h2⟩ := actual_finite_undiscounted_visits_imply_an_event_is_eventually_absent
    (visitEvents 2) path (hp 2)
  refine ⟨max N0 (max N1 N2),fun n hn => ?_⟩
  have hn0 : N0≤n := le_trans (le_max_left _ _) hn
  have hn1 : N1≤n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N2≤n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hp0 := h0 n hn0
  have hp1 := h1 n hn1
  have hp2 := h2 n hn2
  change (path n).1≠(0 : Fin 3).castSucc at hp0
  change (path n).1≠(1 : Fin 3).castSucc at hp1
  change (path n).1≠(2 : Fin 3).castSucc at hp2
  generalize hx : (path n).1=s at *
  fin_cases s <;> norm_num at *

theorem actual_total_transient_visits_are_integrable_and_have_the_true_expectation
    (π : HistoryPolicy (Fin 4) Bool) :
    Integrable totalVisits (law π) ∧
      (∫ path, totalVisits path ∂law π)=(213-28*initialMix π)/95 := by
  have hi (j : Fin 3) : Integrable (visits j) (law π) :=
    (actual_every_history_policy_has_the_true_undiscounted_visit_expectations π j).2.1
  constructor
  · exact integrable_finsetSum Finset.univ (fun j _ => hi j)
  · unfold totalVisits
    rw [integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [(actual_every_history_policy_has_the_true_undiscounted_visit_expectations π _).2.2]
    norm_num [mixedFundamental,fastTransition,pow_two,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply]
    ring

theorem actual_undiscounted_constraint_cost_is_the_number_of_visits_to_state_two
    (π : HistoryPolicy (Fin 4) Bool) :
    Integrable (visits 1) (law π) ∧
      (∫ path, visits 1 path ∂law π)=(28+32*initialMix π)/95 := by
  have h := actual_every_history_policy_has_the_true_undiscounted_visit_expectations π 1
  refine ⟨h.2.1,?_⟩
  rw [h.2.2]
  norm_num [mixedFundamental,fastTransition,pow_two,Matrix.mul_apply,
    Fin.sum_univ_succ,Matrix.one_apply]
  ring

end SafeLearning.CompleteModulesChowTermination21
