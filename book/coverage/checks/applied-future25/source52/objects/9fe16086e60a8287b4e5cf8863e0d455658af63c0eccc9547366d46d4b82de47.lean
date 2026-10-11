import SafeLearning.CompleteAppliedRunningEvaluation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedRunningEvaluationConsequences
open CompleteAppliedRunningEvaluation CompleteFiniteCMDPOccupancy
open CompleteFiniteMarkovPathCorrespondence CompleteFiniteControlledPathMeasure
open CompleteFiniteHistoryPathLinearProgram CompleteFiniteCMDPDeterministicVertices

theorem actual_uniform_value_is_the_integral_of_the_true_infinite_constructed_path_return
    (initial : Fin 2) :
    (∫ path, ∑' n : ℕ, (9/10:ℝ)^n*reward (path n).1 (path n).2
      ∂controlledPathMeasure (model initial) (markovHistoryPolicy uniformPolicy))=uniformValue initial := by
  rw [actual_constructed_markov_path_expected_return _ _ (9/10) (by norm_num) (by norm_num),
    actual_uniform_expected_discounted_return_equals_the_matrix_value]

theorem actual_first_greedy_value_is_the_integral_of_the_true_infinite_constructed_path_return
    (initial : Fin 2) :
    (∫ path, ∑' n : ℕ, (9/10:ℝ)^n*reward (path n).1 (path n).2
      ∂controlledPathMeasure (model initial) (markovHistoryPolicy greedyPolicy))=greedyValue initial := by
  rw [actual_constructed_markov_path_expected_return _ _ (9/10) (by norm_num) (by norm_num),
    (actual_greedy_expected_return_is_derived_and_improves_the_uniform_policy initial).1]

def secondImprovement : Policy (Fin 2) (Fin 2) := purePolicy (fun _ => 1)

theorem actual_second_improvement_action (n : ℕ) (state action : Fin 2) :
    secondImprovement.action n state action=if action=1 then 1 else 0 := by
  simp [secondImprovement,purePolicy,pureAction]

theorem actual_always_field_policy_is_at_field_at_every_positive_time
    (initial state : Fin 2) (n : ℕ) :
    stateMass (model initial) secondImprovement (n+1) state=if state=1 then 1 else 0 := by
  have ht := actual_state_total_mass (model initial) secondImprovement n
  rw [stateMass]
  simp only [actual_model_transition_probability,actual_second_improvement_action]
  fin_cases state <;> norm_num [Fin.sum_univ_succ] at *
  exact ht

theorem actual_one_more_greedy_improvement_attains_the_source_optimal_expected_return
    (initial : Fin 2) :
    expectedReturn (model initial) secondImprovement (9/10) reward=optimalValue initial := by
  have hs := actual_discounted_reward_series_summable (model initial) secondImprovement (9/10)
    (by norm_num) (by norm_num) reward
  unfold expectedReturn
  rw [hs.tsum_eq_zero_add]
  have hstage0 : (∑ s,∑ a,jointMass (model initial) secondImprovement 0 s a*reward s a)=reward initial 1 := by
    simp only [jointMass,stateMass,actual_model_initial_probability,actual_second_improvement_action]
    fin_cases initial <;> norm_num [reward,Fin.sum_univ_succ]
  have hstage : ∀ n, (∑ s,∑ a,jointMass (model initial) secondImprovement (n+1) s a*reward s a)=2 := by
    intro n
    simp only [jointMass,actual_always_field_policy_is_at_field_at_every_positive_time,
      actual_second_improvement_action]
    norm_num [reward,Fin.sum_univ_succ]
  simp only [hstage0,hstage,pow_zero,one_mul,pow_succ]
  rw [tsum_mul_right,tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  fin_cases initial <;> norm_num [reward,optimalValue]

theorem actual_second_improved_constructed_path_attains_the_all_history_optimum (initial : Fin 2) :
    (∫ path, ∑' n : ℕ, (9/10:ℝ)^n*reward (path n).1 (path n).2
      ∂controlledPathMeasure (model initial) (markovHistoryPolicy secondImprovement))=optimalValue initial ∧
      IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
        pathReturn (model initial) (9/10) pi reward=v} (optimalValue initial) := by
  exact ⟨by rw [actual_constructed_markov_path_expected_return _ _ (9/10) (by norm_num) (by norm_num),
    actual_one_more_greedy_improvement_attains_the_source_optimal_expected_return],
    actual_optimal_value_is_the_attained_all_history_path_return_optimum initial⟩

theorem actual_uniform_value_obeys_the_literal_policy_evaluation_bellman_equation :
    uniformValue=fun state => uniformReward state+(9/10)*(uniformTransition *ᵥ uniformValue) state := by
  rw [actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers.1,
    actual_uniform_transition_and_reward_are_derived_from_the_running_mdp.1,
    actual_uniform_transition_and_reward_are_derived_from_the_running_mdp.2]
  funext state
  fin_cases state <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_uniform_home_occupancy_has_the_literal_four_state_action_masses :
    occupancy (model 0) uniformPolicy (9/10)=(!![11/40,11/40;9/40,9/40] : Matrix (Fin 2) (Fin 2) ℝ) := by
  funext state action
  unfold occupancy
  simp only [jointMass,actual_uniform_action_probability]
  simp_rw [←mul_assoc]
  rw [tsum_mul_right]
  change (1-(9/10:ℝ))*(actualVisitSeries 0 state*(1/2))=_
  rw [actual_fundamental_matrix_is_the_derived_discounted_state_visit_series]
  fin_cases state <;> fin_cases action <;> norm_num [sourceFundamental]

def actualHarvestCost (state action : Fin 2) : ℝ := if state=1 ∧ action=1 then 1 else 0

theorem actual_uniform_home_return_and_cost_match_the_true_occupancy_linear_functional :
    expectedReturn (model 0) uniformPolicy (9/10) reward=29/4 ∧
      expectedReturn (model 0) uniformPolicy (9/10) actualHarvestCost=9/4 := by
  constructor
  · rw [actual_uniform_expected_discounted_return_equals_the_matrix_value,
      actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers.1]
    norm_num
  · rw [actual_reward_return_identity _ _ (9/10) (by norm_num) (by norm_num),
      actual_uniform_home_occupancy_has_the_literal_four_state_action_masses]
    norm_num [actualHarvestCost,Fin.sum_univ_succ]

end SafeLearning.CompleteAppliedRunningEvaluationConsequences
