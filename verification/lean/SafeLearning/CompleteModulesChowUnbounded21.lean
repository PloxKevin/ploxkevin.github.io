import SafeLearning.CompleteModulesChowAbsorption21
import SafeLearning.CompleteChowBounds21

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SafeLearning.CompleteModulesChowUnbounded21
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteModulesChowVisitCost21
open SafeLearning.CompleteModulesChowControlled21
open SafeLearning.CompleteModulesChowTermination21
open SafeLearning.CompleteModulesChowAbsorption21
open SafeLearning.CompleteChowLP21
open SafeLearning.CompleteChowBounds21
local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => MeasurableSet.of_discrete⟩

/-- The literal baseline always plays its original action. -/
def baseline : HistoryPolicy (Fin 4) Bool where
  action _ _ _ a := if a then 0 else 1
  action_nonneg _ _ _ a := by cases a <;> norm_num
  action_sum _ _ _ := by simp

theorem actual_path_is_terminal_after_its_first_absorption_time
    (path : ℕ → Fin 4 × Bool) (hex : ∃ n : ℕ, (path n).1=3)
    (habs : ∀ n : ℕ, (path n).1=3 → (path (n+1)).1=3)
    (n : ℕ) (hn : firstAbsorptionTime path≤n) : (path n).1=3 := by
  have hT : (path (firstAbsorptionTime path)).1=3 := by
    simpa only [firstAbsorptionTime,dif_pos hex] using Nat.find_spec hex
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hT
  | succ k ih =>
      exact habs (firstAbsorptionTime path+k) (ih (by omega))

theorem actual_every_history_policy_has_positive_nonterminal_probability_at_arbitrarily_late_times
    (π : HistoryPolicy (Fin 4) Bool) (T : ℕ) :
    ∃ n : ℕ, T<n ∧ 0<(law π).real {path | (path n).1=(1 : Fin 3).castSucc} := by
  obtain ⟨n,hn,hpos⟩ := actual_positive_nonterminal_marginals_at_arbitrarily_late_times
    (initialMix π) (actual_initial_policy_mixing_probability_is_in_the_unit_interval π).1 T
  refine ⟨n,hn,?_⟩
  change 0 < mass π n (1 : Fin 3).castSucc
  rw [actual_every_history_policy_has_the_literal_matrix_power_marginals]
  exact hpos

theorem actual_no_history_policy_has_an_almost_sure_uniform_bound_on_termination_time
    (π : HistoryPolicy (Fin 4) Bool) (T : ℕ) :
    ¬(∀ᵐ path ∂law π, firstAbsorptionTime path≤T) := by
  intro hb
  obtain ⟨n,hn,hpos⟩ :=
    actual_every_history_policy_has_positive_nonterminal_probability_at_arbitrarily_late_times π T
  have he := actual_every_history_policy_terminates_almost_surely π
  have ha := actual_absorbing_state_remains_absorbing_almost_surely_for_every_policy π
  have hnot : ∀ᵐ path ∂law π, path∉{path | (path n).1=(1 : Fin 3).castSucc} := by
    filter_upwards [hb,he,ha] with path hp hterm habs
    obtain ⟨N,hN⟩ := hterm
    have hterminal := actual_path_is_terminal_after_its_first_absorption_time path
      ⟨N,hN N le_rfl⟩ habs n (le_trans hp hn.le)
    change (path n).1≠(1 : Fin 3).castSucc
    rw [hterminal]
    norm_num
  have hz := measure_eq_zero_iff_ae_notMem.mpr hnot
  have hr := (measureReal_eq_zero_iff).mpr hz
  linarith

theorem actual_baseline_expected_visits_cost_and_duration_are_literal_exact_fractions :
    (∫ path, visits 0 path ∂law baseline)=1 ∧
    (∫ path, visits 1 path ∂law baseline)=28/95 ∧
    (∫ path, visits 2 path ∂law baseline)=18/19 ∧
    (∫ path, (firstAbsorptionTime path : ℝ) ∂law baseline)=213/95 := by
  have h0 := (actual_every_history_policy_has_the_true_undiscounted_visit_expectations baseline 0).2.2
  have h1 := (actual_every_history_policy_has_the_true_undiscounted_visit_expectations baseline 1).2.2
  have h2 := (actual_every_history_policy_has_the_true_undiscounted_visit_expectations baseline 2).2.2
  have hT := (actual_every_policy_has_integrable_first_absorption_time_and_literal_expected_duration baseline).2
  norm_num [initialMix,baseline,mixedFundamental,fastTransition,pow_two,
    Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] at h0 h1 h2 hT
  exact ⟨h0,h1,h2,hT⟩

end SafeLearning.CompleteModulesChowUnbounded21
