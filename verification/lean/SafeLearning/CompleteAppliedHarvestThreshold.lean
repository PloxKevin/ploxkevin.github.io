import SafeLearning.CompleteAppliedRunningEvaluationConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedHarvestThreshold
open CompleteAppliedRunningEvaluation CompleteAppliedRunningEvaluationConsequences
open CompleteFiniteCMDPOccupancy CompleteFiniteMarkovPathCorrespondence
open CompleteFiniteControlledPathMeasure CompleteFiniteHistoryPathLinearProgram
open CompleteAppliedBellman CompleteAppliedBellmanReturns CompleteFiniteCMDPDeterministicVertices

def harvestReward (h : ℝ) : Fin 2 → Fin 2 → ℝ := !![1,0;0,h]
def restPolicy : Policy (Fin 2) (Fin 2) := purePolicy (fun _ => 0)
def shuttlePolicy : Policy (Fin 2) (Fin 2) := purePolicy (fun state => if state=0 then 1 else 0)

theorem actual_rest_action (n : ℕ) (state action : Fin 2) :
    restPolicy.action n state action=if action=0 then 1 else 0 := by
  simp [restPolicy,purePolicy,pureAction]

theorem actual_shuttle_action (n : ℕ) (state action : Fin 2) :
    shuttlePolicy.action n state action=if action=(if state=0 then 1 else 0) then 1 else 0 := by
  simp [shuttlePolicy,purePolicy,pureAction]

theorem actual_any_home_resting_pure_policy_stays_home (choose : Fin 2 → Fin 2)
    (hc : choose 0=0) (state : Fin 2) (n : ℕ) :
    stateMass (model 0) (purePolicy choose) n state=if state=0 then 1 else 0 := by
  induction n generalizing state with
  | zero => exact actual_model_initial_probability 0 state
  | succ n ih =>
    rw [stateMass]
    simp only [ih,actual_model_transition_probability]
    fin_cases state <;> norm_num [purePolicy,pureAction,Fin.sum_univ_succ,hc]

theorem actual_home_resting_policy_return_is_the_true_geometric_series
    (choose : Fin 2 → Fin 2) (hc : choose 0=0) (h gamma : ℝ)
    (hg0 : 0≤gamma) (hg1 : gamma<1) :
    expectedReturn (model 0) (purePolicy choose) gamma (harvestReward h)=1/(1-gamma) := by
  have he : expectedReturn (model 0) (purePolicy choose) gamma (harvestReward h)=∑' n : ℕ,gamma^n := by
    unfold expectedReturn
    apply tsum_congr
    intro n
    simp only [jointMass,actual_any_home_resting_pure_policy_stays_home choose hc]
    norm_num [purePolicy,pureAction,harvestReward,Fin.sum_univ_succ,hc]
  rw [he,tsum_geometric_of_lt_one hg0 hg1]
  simp only [one_div]

theorem actual_always_harvest_return_is_derived_from_its_time_zero_and_future_laws
    (h gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) :
    expectedReturn (model 0) secondImprovement gamma (harvestReward h)=gamma*h/(1-gamma) := by
  have hs := actual_discounted_reward_series_summable (model 0) secondImprovement gamma hg0 hg1 (harvestReward h)
  unfold expectedReturn
  rw [hs.tsum_eq_zero_add]
  have hz : (∑ s,∑ a,jointMass (model 0) secondImprovement 0 s a*harvestReward h s a)=0 := by
    simp only [jointMass,stateMass,actual_model_initial_probability,actual_second_improvement_action]
    norm_num [harvestReward,Fin.sum_univ_succ]
  have ht : ∀ n,(∑ s,∑ a,jointMass (model 0) secondImprovement (n+1) s a*harvestReward h s a)=h := by
    intro n
    simp only [jointMass,actual_always_field_policy_is_at_field_at_every_positive_time,actual_second_improvement_action]
    norm_num [harvestReward,Fin.sum_univ_succ]
  simp only [hz,ht,pow_zero,mul_zero,zero_add,pow_succ]
  rw [tsum_mul_right,tsum_mul_right,tsum_geometric_of_lt_one hg0 hg1]
  ring

theorem actual_shuttling_policy_has_zero_reward_at_every_time_and_true_zero_return
    (h gamma : ℝ) :
    (∀ n,(∑ s,∑ a,jointMass (model 0) shuttlePolicy n s a*harvestReward h s a)=0) ∧
      expectedReturn (model 0) shuttlePolicy gamma (harvestReward h)=0 := by
  have hz : ∀ n,(∑ s,∑ a,jointMass (model 0) shuttlePolicy n s a*harvestReward h s a)=0 := by
    intro n
    simp only [jointMass,actual_shuttle_action]
    norm_num [harvestReward,Fin.sum_univ_succ]
  exact ⟨hz,by simp only [expectedReturn,hz,mul_zero,tsum_zero]⟩

theorem actual_four_deterministic_stationary_home_returns (h gamma : ℝ)
    (hg0 : 0≤gamma) (hg1 : gamma<1) :
    expectedReturn (model 0) restPolicy gamma (harvestReward h)=1/(1-gamma) ∧
    expectedReturn (model 0) greedyPolicy gamma (harvestReward h)=1/(1-gamma) ∧
    expectedReturn (model 0) secondImprovement gamma (harvestReward h)=gamma*h/(1-gamma) ∧
    expectedReturn (model 0) shuttlePolicy gamma (harvestReward h)=0 := by
  exact ⟨actual_home_resting_policy_return_is_the_true_geometric_series (fun _ => 0) rfl h gamma hg0 hg1,
    actual_home_resting_policy_return_is_the_true_geometric_series id rfl h gamma hg0 hg1,
    actual_always_harvest_return_is_derived_from_its_time_zero_and_future_laws h gamma hg0 hg1,
    (actual_shuttling_policy_has_zero_reward_at_every_time_and_true_zero_return h gamma).2⟩

def candidateValue (h gamma : ℝ) : Fin 2 → ℝ :=
  if 1≤gamma*h then ![gamma*h/(1-gamma),h/(1-gamma)]
  else if h≤gamma then ![1/(1-gamma),gamma/(1-gamma)]
  else ![1/(1-gamma),h/(1-gamma)]

theorem actual_candidate_is_a_bellman_fixed_point_for_every_positive_harvest_reward
    (h gamma : ℝ) (hh : 0<h) (hg0 : 0<gamma) (hg1 : gamma<1) :
    ∀ state,bellman transition (harvestReward h) gamma (candidateValue h gamma) state=
      candidateValue h gamma state := by
  have hd : 0<1-gamma := sub_pos.mpr hg1
  have hg2 : gamma^2<1 := by nlinarith
  by_cases ha : 1≤gamma*h
  · simp only [candidateValue,ite_eq_left ha]
    intro state
    unfold bellman
    apply le_antisymm
    · apply Finset.sup'_le
      intro action hm
      fin_cases state <;> fin_cases action <;>
        norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
      all_goals (try simp only [←one_div]); apply (le_div_iff₀ hd).2 <;> field_simp <;> nlinarith
    · have hm := Finset.le_sup' (s:=Finset.univ)
        (f:=fun action => harvestReward h state action+gamma*finiteMean (transition state action)
          (![gamma*h/(1-gamma),h/(1-gamma)] : Fin 2 → ℝ)) (Finset.mem_univ (1:Fin 2))
      convert hm using 1
      fin_cases state <;> norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
      all_goals field_simp <;> ring
  · have hgha : gamma*h<1 := lt_of_not_ge ha
    by_cases hb : h≤gamma
    · simp only [candidateValue,ite_eq_right ha,ite_eq_left hb]
      intro state
      unfold bellman
      apply le_antisymm
      · apply Finset.sup'_le
        intro action hm
        fin_cases state <;> fin_cases action <;>
          norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
        all_goals (try simp only [←one_div]); apply (le_div_iff₀ hd).2 <;> field_simp <;> nlinarith
      · have hm := Finset.le_sup' (s:=Finset.univ)
          (f:=fun action => harvestReward h state action+gamma*finiteMean (transition state action)
            (![1/(1-gamma),gamma/(1-gamma)] : Fin 2 → ℝ)) (Finset.mem_univ (0:Fin 2))
        convert hm using 1
        fin_cases state <;> norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
        all_goals field_simp <;> ring
    · have hhg : gamma<h := lt_of_not_ge hb
      simp only [candidateValue,ite_eq_right ha,ite_eq_right hb]
      intro state
      unfold bellman
      apply le_antisymm
      · apply Finset.sup'_le
        intro action hm
        fin_cases state <;> fin_cases action <;>
          norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
        all_goals (try simp only [←one_div]); apply (le_div_iff₀ hd).2 <;> field_simp <;> nlinarith
      · have hm := Finset.le_sup' (s:=Finset.univ)
          (f:=fun action => harvestReward h state action+gamma*finiteMean (transition state action)
            (![1/(1-gamma),h/(1-gamma)] : Fin 2 → ℝ)) (Finset.mem_univ state)
        convert hm using 1
        fin_cases state <;> norm_num [harvestReward,transition,finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
        all_goals field_simp <;> ring

theorem actual_home_optimal_value_is_the_maximum_of_the_two_nonshuttling_values
    (h gamma : ℝ) (_hh : 0<h) (_hg0 : 0<gamma) (hg1 : gamma<1) :
    candidateValue h gamma 0=max (1/(1-gamma)) (gamma*h/(1-gamma)) := by
  have hd : 0<1-gamma := sub_pos.mpr hg1
  by_cases ha : 1≤gamma*h
  · rw [candidateValue,ite_eq_left ha,max_eq_right]
    · rfl
    · exact (div_le_div_iff_of_pos_right hd).2 ha
  · rw [candidateValue,ite_eq_right ha,max_eq_left]
    · split_ifs <;> rfl
    · exact (div_le_div_iff_of_pos_right hd).2 (le_of_lt (lt_of_not_ge ha))

theorem actual_home_maximum_is_attained_over_all_history_dependent_path_policies
    (h gamma : ℝ) (hh : 0<h) (hg0 : 0<gamma) (hg1 : gamma<1) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model 0) gamma pi (harvestReward h)=v}
        (max (1/(1-gamma)) (gamma*h/(1-gamma))) := by
  have hv := actual_bellman_fixed_point_is_the_attained_optimum_over_all_history_paths
    (PMF.pure (0:Fin 2)) transition (harvestReward h) gamma hg0.le hg1
    (candidateValue h gamma) (actual_candidate_is_a_bellman_fixed_point_for_every_positive_harvest_reward h gamma hh hg0 hg1)
  have he : finiteMean (PMF.pure (0:Fin 2)) (candidateValue h gamma)=candidateValue h gamma 0 := by
    simp [finiteMean,PMF.pure_apply,Fin.sum_univ_succ]
  rw [he,actual_home_optimal_value_is_the_maximum_of_the_two_nonshuttling_values h gamma hh hg0 hg1] at hv
  exact hv

theorem actual_harvesting_is_optimal_iff_gamma_times_h_is_at_least_one
    (h gamma : ℝ) (_hh : 0<h) (_hg0 : 0<gamma) (hg1 : gamma<1) :
    (gamma*h/(1-gamma)=max (1/(1-gamma)) (gamma*h/(1-gamma)) ↔ 1≤gamma*h) ∧
    (1/(1-gamma)<gamma*h/(1-gamma) ↔ 1<gamma*h) ∧
    (gamma*h=1 → gamma*h/(1-gamma)=1/(1-gamma)) := by
  have hd : 0<1-gamma := sub_pos.mpr hg1
  constructor
  · rw [eq_comm,max_eq_right_iff,div_le_div_iff_of_pos_right hd]
  constructor
  · exact div_lt_div_iff_of_pos_right hd
  · intro ht
    rw [ht]

theorem actual_harvest_cost_and_source_optimal_feasible_discount_interval
    (gamma : ℝ) (hg0 : 0<gamma) (hg1 : gamma<1) :
    expectedReturn (model 0) secondImprovement gamma actualHarvestCost=gamma/(1-gamma) ∧
    (gamma/(1-gamma)≤9/2 ↔ gamma≤9/11) ∧
    (1≤gamma*2 ∧ gamma/(1-gamma)≤9/2 ↔ gamma∈Icc (1/2:ℝ) (9/11)) := by
  have hd : 0<1-gamma := sub_pos.mpr hg1
  have ht : expectedReturn (model 0) secondImprovement gamma actualHarvestCost=gamma/(1-gamma) := by
    have hs := actual_discounted_reward_series_summable (model 0) secondImprovement gamma hg0.le hg1 actualHarvestCost
    unfold expectedReturn
    rw [hs.tsum_eq_zero_add]
    have hz : (∑ s,∑ a,jointMass (model 0) secondImprovement 0 s a*actualHarvestCost s a)=0 := by
      simp only [jointMass,stateMass,actual_model_initial_probability,actual_second_improvement_action]
      norm_num [actualHarvestCost,Fin.sum_univ_succ]
    have hn : ∀ n,(∑ s,∑ a,jointMass (model 0) secondImprovement (n+1) s a*actualHarvestCost s a)=1 := by
      intro n
      simp only [jointMass,actual_always_field_policy_is_at_field_at_every_positive_time,actual_second_improvement_action]
      norm_num [actualHarvestCost,Fin.sum_univ_succ]
    simp only [hz,hn,pow_zero,mul_zero,zero_add,mul_one,pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_lt_one hg0.le hg1]
    ring
  have hf : gamma/(1-gamma)≤9/2 ↔ gamma≤9/11 := by
    rw [div_le_iff₀ hd]
    constructor <;> intro ht <;> linarith
  exact ⟨ht,hf,by rw [hf]; simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]⟩

theorem actual_threshold_and_effective_horizon_interpretation (gamma : ℝ)
    (_hg0 : 0<gamma) (hg1 : gamma<1) :
    (gamma*2<1 ↔ gamma<1/2) ∧ (1/(1-gamma)<2 ↔ gamma<1/2) ∧
    ((1/2:ℝ)/(1-1/2)=1) ∧
    |(9/11:ℝ)-(818/1000:ℝ)|<1/2000 := by
  have hd : 0<1-gamma := sub_pos.mpr hg1
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · rw [div_lt_iff₀ hd]
    constructor <;> intro h <;> linarith
  norm_num

end SafeLearning.CompleteAppliedHarvestThreshold
