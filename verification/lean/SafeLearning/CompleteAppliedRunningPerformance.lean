import SafeLearning.CompleteAppliedHarvestConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedRunningPerformance
open CompleteAppliedRunningEvaluation CompleteAppliedRunningEvaluationConsequences
open CompleteAppliedHarvestThreshold CompleteAppliedHarvestConsequences
open CompleteFiniteCMDPOccupancy CompleteFiniteMarkovPathCorrespondence
open CompleteFiniteControlledPathMeasure CompleteFiniteHistoryPathLinearProgram
open CompleteAppliedBellman CompleteFiniteCMDPDeterministicVertices

def restValue : Fin 2 → ℝ := ![10,9]
def restQ (state action : Fin 2) : ℝ := reward state action+(9/10)*finiteMean (transition state action) restValue
def restAdvantage (state action : Fin 2) : ℝ := restQ state action-restValue state

theorem actual_home_rest_state_law (state : Fin 2) (n : ℕ) :
    stateMass (model 0) restPolicy n state=if state=0 then 1 else 0 :=
  actual_any_home_resting_pure_policy_stays_home (fun _ => 0) rfl state n

theorem actual_rest_everywhere_state_law_after_the_first_step (initial state : Fin 2) (n : ℕ) :
    stateMass (model initial) restPolicy (n+1) state=if state=0 then 1 else 0 := by
  have ht := actual_state_total_mass (model initial) restPolicy n
  rw [stateMass]
  simp only [actual_model_transition_probability,actual_rest_action]
  fin_cases state <;> norm_num [Fin.sum_univ_succ] at *
  exact ht

theorem actual_rest_value_is_the_true_expected_infinite_return (initial : Fin 2) :
    expectedReturn (model initial) restPolicy (9/10) reward=restValue initial := by
  have hs := actual_discounted_reward_series_summable (model initial) restPolicy (9/10)
    (by norm_num) (by norm_num) reward
  unfold expectedReturn
  rw [hs.tsum_eq_zero_add]
  have hz : (∑ s,∑ a,jointMass (model initial) restPolicy 0 s a*reward s a)=reward initial 0 := by
    simp only [jointMass,stateMass,actual_model_initial_probability,actual_rest_action]
    fin_cases initial <;> norm_num [reward,Fin.sum_univ_succ]
  have hn : ∀ n,(∑ s,∑ a,jointMass (model initial) restPolicy (n+1) s a*reward s a)=1 := by
    intro n
    simp only [jointMass,actual_rest_everywhere_state_law_after_the_first_step,actual_rest_action]
    norm_num [reward,Fin.sum_univ_succ]
  simp only [hz,hn,pow_zero,one_mul,mul_one,pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  fin_cases initial <;> norm_num [reward,restValue]

theorem actual_rest_q_and_advantage_have_all_the_source_entries :
    restQ=(!![10,81/10;9,101/10] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    restAdvantage=(!![0,-19/10;0,11/10] : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · ext s a
    fin_cases s <;> fin_cases a <;> norm_num [restQ,reward,transition,restValue,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
  · ext s a
    fin_cases s <;> fin_cases a <;> norm_num [restAdvantage,restQ,reward,transition,restValue,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]

theorem actual_rest_and_harvest_discounted_joint_occupancies_are_derived_from_the_real_laws :
    occupancy (model 0) restPolicy (9/10)=(!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    occupancy (model 0) secondImprovement (9/10)=(!![0,1/10;0,9/10] : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · funext state action
    unfold occupancy
    simp only [jointMass,actual_home_rest_state_law,actual_rest_action]
    fin_cases state <;> fin_cases action <;> norm_num
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · funext state action
    have hs := actual_joint_discounted_series_summable (model 0) secondImprovement (9/10)
      (by norm_num) (by norm_num) state action
    unfold occupancy
    rw [hs.tsum_eq_zero_add]
    have hz (s : Fin 2) : stateMass (model 0) secondImprovement 0 s=if s=0 then 1 else 0 :=
      actual_model_initial_probability 0 s
    simp only [jointMass,hz,
      actual_always_field_policy_is_at_field_at_every_positive_time,actual_second_improvement_action,
      pow_zero,one_mul,pow_succ]
    fin_cases state <;> fin_cases action <;> norm_num
    rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num

def restStateOccupancy (state : Fin 2) : ℝ := ∑ action,occupancy (model 0) restPolicy (9/10) state action
def harvestStateOccupancy (state : Fin 2) : ℝ := ∑ action,occupancy (model 0) secondImprovement (9/10) state action

theorem actual_source_normalized_state_occupancies_and_support_difference :
    restStateOccupancy=(![1,0] : Fin 2 → ℝ) ∧
    harvestStateOccupancy=(![1/10,9/10] : Fin 2 → ℝ) ∧ restStateOccupancy 1=0 := by
  have ho := actual_rest_and_harvest_discounted_joint_occupancies_are_derived_from_the_real_laws
  constructor
  · funext s
    rw [restStateOccupancy,ho.1]
    fin_cases s <;> norm_num [Fin.sum_univ_succ]
  constructor
  · funext s
    rw [harvestStateOccupancy,ho.2]
    fin_cases s <;> norm_num [Fin.sum_univ_succ]
  rw [restStateOccupancy,ho.1]
  norm_num [Fin.sum_univ_succ]

def actualPerformanceExpression : ℝ :=
  (1/(1-9/10:ℝ))*∑ state,harvestStateOccupancy state*∑ action,
    secondImprovement.action 0 state action*restAdvantage state action
def actualSurrogate : ℝ :=
  expectedReturn (model 0) restPolicy (9/10) reward+
    (1/(1-9/10:ℝ))*∑ state,restStateOccupancy state*∑ action,
      secondImprovement.action 0 state action*restAdvantage state action

theorem actual_performance_difference_expression_equals_the_true_path_return_difference :
    actualPerformanceExpression=8 ∧
    expectedReturn (model 0) secondImprovement (9/10) reward-
      expectedReturn (model 0) restPolicy (9/10) reward=actualPerformanceExpression ∧
    pathReturn (model 0) (9/10) (markovHistoryPolicy secondImprovement) reward-
      pathReturn (model 0) (9/10) (markovHistoryPolicy restPolicy) reward=8 := by
  have hp : actualPerformanceExpression=8 := by
    rw [actualPerformanceExpression,actual_source_normalized_state_occupancies_and_support_difference.2.1,
      actual_rest_q_and_advantage_have_all_the_source_entries.2]
    norm_num [actual_second_improvement_action,Fin.sum_univ_succ]
  refine ⟨hp,?_,?_⟩
  · rw [actual_one_more_greedy_improvement_attains_the_source_optimal_expected_return,
      actual_rest_value_is_the_true_expected_infinite_return,hp]
    norm_num [optimalValue,restValue]
  · rw [pathReturn,pathReturn,actual_constructed_markov_path_expected_return _ _ (9/10) (by norm_num) (by norm_num),
      actual_constructed_markov_path_expected_return _ _ (9/10) (by norm_num) (by norm_num),
      actual_one_more_greedy_improvement_attains_the_source_optimal_expected_return,
      actual_rest_value_is_the_true_expected_infinite_return]
    norm_num [optimalValue,restValue]

theorem actual_sum_surrogate_is_minus_nine_and_the_importance_ratio_support_condition_fails :
    actualSurrogate=-9 ∧
      secondImprovement.action 0 0 1=1 ∧ restPolicy.action 0 0 1=0 ∧
      ¬(∀ s a,0<secondImprovement.action 0 s a→0<restPolicy.action 0 s a) := by
  have hz : actualSurrogate=-9 := by
    rw [actualSurrogate,actual_rest_value_is_the_true_expected_infinite_return,
      actual_source_normalized_state_occupancies_and_support_difference.1,
      actual_rest_q_and_advantage_have_all_the_source_entries.2]
    norm_num [restValue,actual_second_improvement_action,Fin.sum_univ_succ]
  refine ⟨hz,by norm_num [actual_second_improvement_action],by norm_num [actual_rest_action],?_⟩
  intro hc
  have h := hc (0:Fin 2) (1:Fin 2) (by norm_num [actual_second_improvement_action])
  norm_num [actual_rest_action] at h

def oldDataRatioAverage (ratio : Fin 2 → Fin 2 → ℝ) : ℝ :=
  expectedReturn (model 0) restPolicy (9/10) reward+
    10*∑ s,∑ a,occupancy (model 0) restPolicy (9/10) s a*ratio s a*restAdvantage s a

theorem actual_old_data_ratio_weighted_average_is_blind_for_every_supplied_ratio
    (ratio : Fin 2 → Fin 2 → ℝ) : oldDataRatioAverage ratio=10 := by
  rw [oldDataRatioAverage,actual_rest_value_is_the_true_expected_infinite_return,
    actual_rest_and_harvest_discounted_joint_occupancies_are_derived_from_the_real_laws.1,
    actual_rest_q_and_advantage_have_all_the_source_entries.2]
  norm_num [restValue,Fin.sum_univ_succ]

theorem actual_old_policy_path_contains_only_home_rest_at_every_time_almost_surely :
    ∀ᵐ path ∂controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy),
      ∀ n : ℕ,path n=((0:Fin 2),(0:Fin 2)) := by
  apply ae_all_iff.mpr
  intro n
  let mu := controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy)
  have he : mu.real {path | path n=((0:Fin 2),(0:Fin 2))}=1 := by
    rw [actual_constructed_markov_path_joint_mass]
    simp only [jointMass,actual_home_rest_state_law,actual_rest_action]
    norm_num
  have hm : MeasurableSet {path : ℕ → Fin 2 × Fin 2 | path n=((0:Fin 2),(0:Fin 2))} :=
    (measurableSet_singleton _).preimage (measurable_pi_apply n)
  apply (ae_mem_iff_measure_eq hm.nullMeasurableSet).2
  rw [measure_univ]
  exact (ENNReal.toReal_eq_one_iff _).mp he

def actualRecordedPath (h : ℝ) (path : ℕ → Fin 2 × Fin 2) : ℕ → (Fin 2 × Fin 2) × ℝ :=
  fun n => (path n,harvestReward h (path n).1 (path n).2)

theorem actual_complete_old_observation_law_cannot_distinguish_two_harvest_rewards (h k : ℝ) :
    (controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy)).map (actualRecordedPath h)=
      (controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy)).map (actualRecordedPath k) := by
  apply Measure.map_congr
  filter_upwards [actual_old_policy_path_contains_only_home_rest_at_every_time_almost_surely] with path hp
  funext n
  simp only [actualRecordedPath,hp n]
  norm_num [harvestReward]

theorem actual_identical_old_data_can_hide_distinct_postdeparture_values :
    (controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy)).map (actualRecordedPath 1)=
      (controlledPathMeasure (model 0) (markovHistoryPolicy restPolicy)).map (actualRecordedPath 2) ∧
    expectedReturn (model 0) secondImprovement (9/10) (harvestReward 1)=9 ∧
    expectedReturn (model 0) secondImprovement (9/10) (harvestReward 2)=18 := by
  refine ⟨actual_complete_old_observation_law_cannot_distinguish_two_harvest_rewards 1 2,?_,?_⟩
  all_goals rw [actual_always_harvest_return_is_derived_from_its_time_zero_and_future_laws _ _ (by norm_num) (by norm_num)]; norm_num

end SafeLearning.CompleteAppliedRunningPerformance
