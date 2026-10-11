import SafeLearning.CompleteAppliedBellmanReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedRunningEvaluation
open CompleteFiniteCMDPOccupancy CompleteFiniteMarkovPathCorrespondence
open CompleteFiniteControlledPathMeasure CompleteFiniteHistoryPathLinearProgram
open CompleteAppliedBellman CompleteAppliedBellmanReturns CompleteFiniteCMDPDeterministicVertices

def transition (_state action : Fin 2) : PMF (Fin 2) := PMF.pure action
def reward : Fin 2 → Fin 2 → ℝ := !![1,0;0,2]
def model (initial : Fin 2) : Model (Fin 2) (Fin 2) :=
  actualPMFModel (PMF.pure initial) transition

def uniformPolicy : Policy (Fin 2) (Fin 2) where
  action _ _ _ := 1/2
  action_nonneg _ _ _ := by norm_num
  action_sum _ _ := by norm_num [Fin.sum_univ_succ]

theorem actual_model_initial_probability (initial state : Fin 2) :
    (model initial).initial state = if state=initial then 1 else 0 := by
  change (PMF.pure initial state).toReal = _
  rw [PMF.pure_apply]
  by_cases h : state=initial <;> simp [h]

theorem actual_model_transition_probability (initial state action next : Fin 2) :
    (model initial).transition state action next = if next=action then 1 else 0 := by
  change (PMF.pure action next).toReal = _
  rw [PMF.pure_apply]
  by_cases h : next=action <;> simp [h]

theorem actual_uniform_action_probability (n : ℕ) (state action : Fin 2) :
    uniformPolicy.action n state action=1/2 := rfl

def uniformTransition : Matrix (Fin 2) (Fin 2) ℝ :=
  fun s t => ∑ a, uniformPolicy.action 0 s a * ((transition s a t).toReal)
def uniformReward (s : Fin 2) : ℝ := ∑ a, uniformPolicy.action 0 s a * reward s a

theorem actual_uniform_transition_and_reward_are_derived_from_the_running_mdp :
    uniformTransition = (!![1/2,1/2;1/2,1/2] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      uniformReward = (![1/2,1] : Fin 2 → ℝ) := by
  constructor
  · ext s t
    fin_cases s <;> fin_cases t <;> norm_num [uniformTransition, uniformPolicy, transition,
      PMF.pure_apply, Fin.sum_univ_succ]
  · funext s
    fin_cases s <;> norm_num [uniformReward, uniformPolicy, reward, Fin.sum_univ_succ]

def sourceResolvent : Matrix (Fin 2) (Fin 2) ℝ := 1-(9/10:ℝ) • uniformTransition
def sourceFundamental : Matrix (Fin 2) (Fin 2) ℝ := !![11/2,9/2;9/2,11/2]

theorem actual_source_resolvent_entries_determinant_and_true_two_sided_inverse :
    sourceResolvent = (!![11/20,-9/20;-9/20,11/20] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    sourceResolvent.det = 1/10 ∧ sourceResolvent⁻¹ = sourceFundamental ∧
      sourceResolvent*sourceFundamental=1 ∧ sourceFundamental*sourceResolvent=1 := by
  have he : sourceResolvent = (!![11/20,-9/20;-9/20,11/20] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [sourceResolvent, actual_uniform_transition_and_reward_are_derived_from_the_running_mdp.1]
    ext s t
    fin_cases s <;> fin_cases t <;> norm_num [Matrix.sub_apply, Matrix.smul_apply]
  have hright : sourceResolvent*sourceFundamental=1 := by
    rw [he]
    ext s t
    fin_cases s <;> fin_cases t <;> norm_num [sourceFundamental, Matrix.mul_apply, Fin.sum_univ_succ]
  have hleft : sourceFundamental*sourceResolvent=1 := by
    rw [he]
    ext s t
    fin_cases s <;> fin_cases t <;> norm_num [sourceFundamental, Matrix.mul_apply, Fin.sum_univ_succ]
  exact ⟨he, by rw [he, Matrix.det_fin_two]; norm_num,
    Matrix.inv_eq_right_inv hright, hright, hleft⟩

theorem actual_uniform_state_law_at_every_positive_time_is_derived
    (initial state : Fin 2) (n : ℕ) : stateMass (model initial) uniformPolicy (n+1) state=1/2 := by
  have ht := actual_state_total_mass (model initial) uniformPolicy n
  rw [stateMass]
  simp only [actual_model_transition_probability, actual_uniform_action_probability]
  fin_cases state <;> norm_num [Fin.sum_univ_succ] at * <;> linarith

theorem actual_uniform_initial_state_law (initial state : Fin 2) :
    stateMass (model initial) uniformPolicy 0 state=if state=initial then 1 else 0 := by
  exact actual_model_initial_probability initial state

def actualVisitSeries (initial state : Fin 2) : ℝ :=
  ∑' n : ℕ, (9/10:ℝ)^n * stateMass (model initial) uniformPolicy n state

theorem actual_fundamental_matrix_is_the_derived_discounted_state_visit_series
    (initial state : Fin 2) : actualVisitSeries initial state=sourceFundamental initial state := by
  have hs := actual_state_discounted_series_summable (model initial) uniformPolicy (9/10)
    (by norm_num) (by norm_num) state
  rw [actualVisitSeries, hs.tsum_eq_zero_add]
  simp only [actual_uniform_initial_state_law, actual_uniform_state_law_at_every_positive_time_is_derived,
    pow_zero, one_mul, pow_succ]
  have ht : (∑' n : ℕ, (9/10:ℝ)^n*(9/10)*(1/2))=9/2 := by
    rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [ht]
  fin_cases initial <;> fin_cases state <;> norm_num [sourceFundamental]

theorem actual_fundamental_rows_sum_to_the_discounted_total_visit_count (initial : Fin 2) :
    (∑ state, sourceFundamental initial state)=10 ∧ (10:ℝ)=1/(1-9/10) := by
  fin_cases initial <;> norm_num [sourceFundamental, Fin.sum_univ_succ]

theorem actual_fundamental_entries_are_true_expected_discounted_visit_counts
    (initial state : Fin 2) :
    (∫ path, ∑' n : ℕ, (9/10:ℝ)^n*(if (path n).1=state then (1:ℝ) else 0)
      ∂controlledPathMeasure (model initial) (markovHistoryPolicy uniformPolicy))=
        sourceFundamental initial state := by
  rw [actual_constructed_markov_path_expected_return (model initial) uniformPolicy (9/10)
    (by norm_num) (by norm_num) (fun (s _ : Fin 2) => if s=state then (1:ℝ) else 0)]
  change expectedReturn (model initial) uniformPolicy (9/10) (fun s _ => if s=state then 1 else 0)=_
  have he : expectedReturn (model initial) uniformPolicy (9/10) (fun s _ => if s=state then 1 else 0)=
      actualVisitSeries initial state := by
    unfold expectedReturn actualVisitSeries
    apply tsum_congr
    intro n
    congr 1
    simp only [jointMass, actual_uniform_action_probability]
    fin_cases state <;> norm_num [Fin.sum_univ_succ] <;> ring
  rw [he, actual_fundamental_matrix_is_the_derived_discounted_state_visit_series]

theorem actual_uniform_state_occupancy_is_the_true_normalized_fundamental_row
    (initial state : Fin 2) :
    (∑ action, occupancy (model initial) uniformPolicy (9/10) state action)=
      (1/10)*sourceFundamental initial state := by
  rw [actual_occupancy_state_marginal _ _ (9/10) (by norm_num) (by norm_num)]
  change (1-(9/10:ℝ))*actualVisitSeries initial state=_
  rw [actual_fundamental_matrix_is_the_derived_discounted_state_visit_series]
  ring

def uniformValue : Fin 2 → ℝ := sourceFundamental *ᵥ uniformReward

theorem actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers :
    uniformValue=(![29/4,31/4] : Fin 2 → ℝ) ∧
      (fun state => ∑ action, occupancy (model 0) uniformPolicy (9/10) state action)=
        (![11/20,9/20] : Fin 2 → ℝ) := by
  constructor
  · rw [uniformValue, actual_uniform_transition_and_reward_are_derived_from_the_running_mdp.2]
    ext s
    fin_cases s <;> norm_num [sourceFundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · funext s
    rw [actual_uniform_state_occupancy_is_the_true_normalized_fundamental_row]
    fin_cases s <;> norm_num [sourceFundamental]

theorem actual_uniform_expected_discounted_return_equals_the_matrix_value (initial : Fin 2) :
    expectedReturn (model initial) uniformPolicy (9/10) reward=uniformValue initial := by
  unfold expectedReturn
  have hs := actual_discounted_reward_series_summable (model initial) uniformPolicy (9/10)
    (by norm_num) (by norm_num) reward
  rw [hs.tsum_eq_zero_add]
  have hstage0 : (∑ s, ∑ a, jointMass (model initial) uniformPolicy 0 s a*reward s a)=uniformReward initial := by
    simp only [jointMass, actual_uniform_initial_state_law]
    fin_cases initial <;> norm_num [uniformReward, uniformPolicy, reward, Fin.sum_univ_succ]
  have hstage : ∀ n : ℕ, (∑ s, ∑ a, jointMass (model initial) uniformPolicy (n+1) s a*reward s a)=3/4 := by
    intro n
    simp only [jointMass, actual_uniform_state_law_at_every_positive_time_is_derived, actual_uniform_action_probability]
    norm_num [reward, Fin.sum_univ_succ]
  simp only [hstage0, hstage, pow_zero, one_mul, pow_succ]
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers.1,
    actual_uniform_transition_and_reward_are_derived_from_the_running_mdp.2]
  fin_cases initial <;> norm_num

def greedyPolicy : Policy (Fin 2) (Fin 2) := purePolicy id
theorem actual_greedy_action_probability (n : ℕ) (state action : Fin 2) :
    greedyPolicy.action n state action=if action=state then 1 else 0 := by
  simp [greedyPolicy,purePolicy,pureAction]

def greedyValue : Fin 2 → ℝ := ![10,20]
def uniformQ (state action : Fin 2) : ℝ := reward state action+(9/10)*finiteMean (transition state action) uniformValue

theorem actual_uniform_action_values_are_the_literal_q_matrix :
    uniformQ=(!![301/40,279/40;261/40,359/40] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext s a
  rw [uniformQ, actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers.1]
  fin_cases s <;> fin_cases a <;> norm_num [reward, transition, finiteMean, PMF.pure_apply, Fin.sum_univ_succ]

theorem actual_greedy_choice_is_the_unique_source_action_in_each_state (state action : Fin 2) :
    uniformQ state action≤uniformQ state state ∧ (uniformQ state action=uniformQ state state ↔ action=state) := by
  rw [actual_uniform_action_values_are_the_literal_q_matrix]
  fin_cases state <;> fin_cases action <;> norm_num

theorem actual_greedy_state_law_remains_at_its_initial_state (initial state : Fin 2) (n : ℕ) :
    stateMass (model initial) greedyPolicy n state=if state=initial then 1 else 0 := by
  induction n generalizing state with
  | zero => exact actual_uniform_initial_state_law initial state
  | succ n ih =>
    rw [stateMass]
    simp only [ih, actual_greedy_action_probability, actual_model_transition_probability]
    fin_cases initial <;> fin_cases state <;> norm_num [Fin.sum_univ_succ]

theorem actual_greedy_expected_return_is_derived_and_improves_the_uniform_policy (initial : Fin 2) :
    expectedReturn (model initial) greedyPolicy (9/10) reward=greedyValue initial ∧
      uniformValue initial≤greedyValue initial := by
  have he : expectedReturn (model initial) greedyPolicy (9/10) reward=
      ∑' n : ℕ, (9/10:ℝ)^n*reward initial initial := by
    unfold expectedReturn
    apply tsum_congr
    intro n
    congr 1
    simp only [jointMass, actual_greedy_state_law_remains_at_its_initial_state, actual_greedy_action_probability]
    fin_cases initial <;> norm_num [reward, Fin.sum_univ_succ]
  rw [he, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [actual_matrix_policy_value_and_home_state_occupancy_have_the_literal_numbers.1]
  fin_cases initial <;> norm_num [reward, greedyValue]

def optimalValue : Fin 2 → ℝ := ![18,20]

theorem actual_source_optimal_value_is_a_true_bellman_fixed_point :
    ∀ state, bellman transition reward (9/10) optimalValue state=optimalValue state := by
  intro state
  unfold bellman
  apply le_antisymm
  · apply Finset.sup'_le
    intro action ha
    fin_cases state <;> fin_cases action <;>
      norm_num [transition, reward, optimalValue, finiteMean, PMF.pure_apply, Fin.sum_univ_succ]
  · have h := Finset.le_sup' (s := Finset.univ) (f := fun action => reward state action+
      (9/10)*finiteMean (transition state action) optimalValue) (Finset.mem_univ (1:Fin 2))
    convert h using 1
    fin_cases state <;> norm_num [transition, reward, optimalValue, finiteMean, PMF.pure_apply, Fin.sum_univ_succ]

theorem actual_optimal_value_is_the_attained_all_history_path_return_optimum (initial : Fin 2) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model initial) (9/10) pi reward=v} (optimalValue initial) := by
  have h := actual_bellman_fixed_point_is_the_attained_optimum_over_all_history_paths
    (PMF.pure initial) transition reward (9/10) (by norm_num) (by norm_num) optimalValue
    actual_source_optimal_value_is_a_true_bellman_fixed_point
  fin_cases initial <;> simpa [model, finiteMean, PMF.pure_apply, eq_comm, Fin.sum_univ_succ] using h

theorem actual_first_greedy_policy_is_not_optimal_and_one_more_improvement_has_source_value :
    greedyValue 0<optimalValue 0 ∧ greedyValue 1=optimalValue 1 ∧
      (∀ state action : Fin 2, reward state action+(9/10)*finiteMean (transition state action) greedyValue ≤
        reward state 1+(9/10)*finiteMean (transition state 1) greedyValue) := by
  refine ⟨by norm_num [greedyValue,optimalValue],by norm_num [greedyValue,optimalValue],?_⟩
  intro state action
  fin_cases state <;> fin_cases action <;>
    norm_num [reward,transition,greedyValue,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]

end SafeLearning.CompleteAppliedRunningEvaluation
