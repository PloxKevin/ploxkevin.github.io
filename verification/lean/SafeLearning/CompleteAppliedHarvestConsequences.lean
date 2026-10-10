import SafeLearning.CompleteAppliedHarvestConstrained

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedHarvestConsequences
open CompleteAppliedRunningEvaluation CompleteAppliedRunningEvaluationConsequences
open CompleteAppliedHarvestThreshold CompleteAppliedHarvestConstrained
open CompleteFiniteCMDPOccupancy CompleteFiniteMarkovPathCorrespondence
open CompleteFiniteControlledPathMeasure CompleteFiniteHistoryPathLinearProgram
open CompleteFiniteCMDPDeterministicVertices

theorem actual_always_harvest_constructed_infinite_path_return (h gamma : ℝ)
    (hg0 : 0≤gamma) (hg1 : gamma<1) :
    pathReturn (model 0) gamma (markovHistoryPolicy secondImprovement) (harvestReward h)=gamma*h/(1-gamma) := by
  rw [pathReturn,actual_constructed_markov_path_expected_return _ _ gamma hg0 hg1,
    actual_always_harvest_return_is_derived_from_its_time_zero_and_future_laws h gamma hg0 hg1]

theorem actual_home_resting_constructed_path_return (choose : Fin 2 → Fin 2)
    (hc : choose 0=0) (h gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) :
    pathReturn (model 0) gamma (markovHistoryPolicy (purePolicy choose)) (harvestReward h)=1/(1-gamma) := by
  rw [pathReturn,actual_constructed_markov_path_expected_return _ _ gamma hg0 hg1,
    actual_home_resting_policy_return_is_the_true_geometric_series choose hc h gamma hg0 hg1]

theorem actual_always_harvest_is_an_all_history_global_optimizer_iff_the_source_threshold
    (h gamma : ℝ) (hh : 0<h) (hg0 : 0<gamma) (hg1 : gamma<1) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model 0) gamma pi (harvestReward h)=v} (gamma*h/(1-gamma)) ↔ 1≤gamma*h := by
  have ho := actual_home_maximum_is_attained_over_all_history_dependent_path_policies h gamma hh hg0 hg1
  have he := (actual_harvesting_is_optimal_iff_gamma_times_h_is_at_least_one h gamma hh hg0 hg1).1
  constructor
  · intro hp
    exact he.mp (le_antisymm (ho.2 hp.1) (hp.2 ho.1))
  · intro ht
    rwa [←he.mpr ht] at ho

theorem actual_threshold_tie_gives_two_actual_path_global_optimizers
    (h gamma : ℝ) (hh : 0<h) (hg0 : 0<gamma) (hg1 : gamma<1) (ht : gamma*h=1) :
    pathReturn (model 0) gamma (markovHistoryPolicy restPolicy) (harvestReward h)=1/(1-gamma) ∧
    pathReturn (model 0) gamma (markovHistoryPolicy secondImprovement) (harvestReward h)=1/(1-gamma) ∧
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model 0) gamma pi (harvestReward h)=v} (1/(1-gamma)) := by
  have hr := actual_home_resting_constructed_path_return (fun _ => 0) rfl h gamma hg0.le hg1
  have hb := actual_always_harvest_constructed_infinite_path_return h gamma hg0.le hg1
  have ho := (actual_always_harvest_is_an_all_history_global_optimizer_iff_the_source_threshold h gamma hh hg0 hg1).mpr ht.ge
  rw [ht] at hb ho
  exact ⟨hr,hb,ho⟩

theorem actual_every_feasible_deterministic_stationary_policy_is_strictly_suboptimal_above_the_budget_cutoff
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1) (choose : Fin 2 → Fin 2)
    (hc : expectedReturn (model 0) (purePolicy choose) gamma actualHarvestCost≤9/2) :
    expectedReturn (model 0) (purePolicy choose) gamma (harvestReward 2)<optimalReturn gamma := by
  have hg0 : 0<gamma := by linarith
  have ho := (actual_constrained_optimum_strictly_exceeds_resting_and_requires_nonpure_source_flow gamma hg hg1).1
  by_cases h0 : choose 0=0
  · rw [actual_home_resting_policy_return_is_the_true_geometric_series choose h0 2 gamma hg0.le hg1]
    exact ho
  · have h01 : choose 0=1 := by omega
    by_cases h1 : choose 1=0
    · have he : choose=(fun state : Fin 2 => if state=0 then 1 else 0) := by
        funext state
        fin_cases state <;> simp [h01,h1]
      rw [he]
      change expectedReturn (model 0) shuttlePolicy gamma (harvestReward 2)<optimalReturn gamma
      rw [(actual_shuttling_policy_has_zero_reward_at_every_time_and_true_zero_return 2 gamma).2]
      exact lt_trans (div_pos (by norm_num) (sub_pos.mpr hg1)) ho
    · have h11 : choose 1=1 := by omega
      have he : choose=(fun _ : Fin 2 => 1) := by
        funext state
        fin_cases state <;> simp [h01,h11]
      rw [he] at hc
      change expectedReturn (model 0) secondImprovement gamma actualHarvestCost≤9/2 at hc
      have hf := actual_harvest_cost_and_source_optimal_feasible_discount_interval gamma hg0 hg1
      rw [hf.1] at hc
      have hx := hf.2.1.mp hc
      exact False.elim (not_le_of_gt hg hx)

theorem actual_budget_cutoff_source_interval_refers_to_true_path_optimality_and_cost
    (gamma : ℝ) (hg0 : 0<gamma) (hg1 : gamma<1) :
    (IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model 0) gamma pi (harvestReward 2)=v} (gamma*2/(1-gamma)) ∧
      pathReturn (model 0) gamma (markovHistoryPolicy secondImprovement) actualHarvestCost≤9/2) ↔
      gamma∈Icc (1/2:ℝ) (9/11) := by
  rw [actual_always_harvest_is_an_all_history_global_optimizer_iff_the_source_threshold 2 gamma (by norm_num) hg0 hg1]
  have hc : pathReturn (model 0) gamma (markovHistoryPolicy secondImprovement) actualHarvestCost=gamma/(1-gamma) := by
    rw [pathReturn,actual_constructed_markov_path_expected_return _ _ gamma hg0.le hg1,
      (actual_harvest_cost_and_source_optimal_feasible_discount_interval gamma hg0 hg1).1]
  rw [hc]
  exact (actual_harvest_cost_and_source_optimal_feasible_discount_interval gamma hg0 hg1).2.2

end SafeLearning.CompleteAppliedHarvestConsequences
