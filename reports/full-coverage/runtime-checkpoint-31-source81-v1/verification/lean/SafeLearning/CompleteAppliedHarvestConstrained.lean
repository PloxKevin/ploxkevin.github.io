import SafeLearning.CompleteAppliedHarvestThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteAppliedHarvestConstrained
open CompleteAppliedRunningEvaluation CompleteAppliedRunningEvaluationConsequences CompleteAppliedHarvestThreshold
open CompleteFiniteCMDPOccupancy CompleteFiniteCMDPFlow CompleteFiniteCMDPRecovery CompleteFiniteCMDPLinearProgram
open CompleteFiniteMarkovPathCorrespondence CompleteFiniteControlledPathMeasure
open CompleteFiniteControlledPathMeasureLaws CompleteFiniteHistoryPathLinearProgram

def optimalFlow (gamma : ℝ) : Fin 2 → Fin 2 → ℝ :=
  !![1-(9/2)*(1-gamma)/gamma,(9/2)*(1-gamma)^2/gamma;0,(9/2)*(1-gamma)]
def optimalReturn (gamma : ℝ) : ℝ := (1+(2-1/gamma)*(9/2)*(1-gamma))/(1-gamma)

theorem actual_source_constrained_flow_is_nonnegative_and_satisfies_true_bellman_flow
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1) : FlowFeasible (model 0) gamma (optimalFlow gamma) := by
  have hg0 : 0<gamma := by linarith
  have hd : 0<1-gamma := sub_pos.mpr hg1
  constructor
  · intro s a
    fin_cases s <;> fin_cases a
    · change 0≤1-(9/2)*(1-gamma)/gamma
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hg0).2
      linarith
    · change 0≤(9/2:ℝ)*(1-gamma)^2/gamma
      positivity
    · norm_num [optimalFlow]
    · change 0≤(9/2:ℝ)*(1-gamma)
      positivity
  · intro s
    simp only [stateMarginal,actual_model_initial_probability,actual_model_transition_probability]
    fin_cases s <;> norm_num [optimalFlow,Fin.sum_univ_succ]
    all_goals field_simp <;> ring

theorem actual_source_constrained_flow_cost_and_reward_are_derived
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1) :
    rewardFunctional actualHarvestCost (optimalFlow gamma)/(1-gamma)=9/2 ∧
    rewardFunctional (harvestReward 2) (optimalFlow gamma)/(1-gamma)=optimalReturn gamma := by
  have hg0 : 0<gamma := by linarith
  have hd : 0<1-gamma := sub_pos.mpr hg1
  constructor
  · norm_num [rewardFunctional,actualHarvestCost,optimalFlow,Fin.sum_univ_succ]
    field_simp <;> ring
  · norm_num [rewardFunctional,harvestReward,optimalFlow,optimalReturn,Fin.sum_univ_succ]
    field_simp <;> ring

theorem actual_every_cost_feasible_flow_has_the_source_constrained_reward_upper_bound
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1)
    (rho : Fin 2 → Fin 2 → ℝ) (hr : FlowFeasible (model 0) gamma rho)
    (hc : rewardFunctional actualHarvestCost rho≤(1-gamma)*(9/2)) :
    rewardFunctional (harvestReward 2) rho/(1-gamma)≤optimalReturn gamma := by
  have hg0 : 0<gamma := by linarith
  have hd : 0<1-gamma := sub_pos.mpr hg1
  have hcoeff : 0<2*gamma-1 := by linarith
  have ht := actual_all_feasible_flows_have_total_mass_one (model 0) gamma hg1 rho hr
  have hf := hr.2 (1:Fin 2)
  simp only [stateMarginal,actual_model_initial_probability,actual_model_transition_probability] at hf
  norm_num [Fin.sum_univ_succ] at ht hf
  have hn := hr.1 (1:Fin 2) (0:Fin 2)
  have hmul := mul_nonneg (show 0≤1+gamma by linarith) hn
  norm_num [rewardFunctional,actualHarvestCost,Fin.sum_univ_succ] at hc
  have hcost := mul_le_mul_of_nonneg_left hc hcoeff.le
  have hid : gamma*(rho 0 0+2*rho 1 1)+(1+gamma)*rho 1 0=
      gamma+(2*gamma-1)*rho 1 1 := by nlinarith [hf,ht]
  have hbound : gamma*(rho 0 0+2*rho 1 1)≤gamma+(2*gamma-1)*(1-gamma)*(9/2) := by
    nlinarith [hid,hcost]
  norm_num [rewardFunctional,harvestReward,Fin.sum_univ_succ]
  apply (div_le_div_iff_of_pos_right hd).2
  -- The target is the literal linear-program objective before normalization.
  rw [show rho 1 1*2=2*rho 1 1 by ring]
  apply (mul_le_mul_iff_right₀ hg0).mp
  convert hbound using 1 <;> field_simp <;> ring

theorem actual_all_history_constrained_optimum_is_attained_by_a_constructed_stationary_path
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
      pathReturn (model 0) gamma pi actualHarvestCost≤9/2 ∧
      pathReturn (model 0) gamma pi (harvestReward 2)=v} (optimalReturn gamma) := by
  have hg0 : 0≤gamma := by linarith
  have hr := actual_source_constrained_flow_is_nonnegative_and_satisfies_true_bellman_flow gamma hg hg1
  obtain ⟨pi,_,hpi⟩ := actual_every_feasible_flow_has_a_constructed_stationary_path
    (model 0) (0:Fin 2) gamma hg0 hg1 (optimalFlow gamma) hr
  change pathOccupancy (model 0) gamma pi=optimalFlow gamma at hpi
  constructor
  · refine ⟨pi,?_,?_⟩
    · rw [actual_history_path_return_linear_formula _ _ hg0 hg1, hpi,
        (actual_source_constrained_flow_cost_and_reward_are_derived gamma hg hg1).1]
    · rw [actual_history_path_return_linear_formula _ _ hg0 hg1,hpi,
        (actual_source_constrained_flow_cost_and_reward_are_derived gamma hg hg1).2]
  · rintro v ⟨psi,hcost,rfl⟩
    have hflow := actual_all_history_policies_have_flow_feasible_path_occupancy (model 0) psi gamma hg0 hg1
    rw [actual_history_path_return_linear_formula _ _ hg0 hg1] at hcost ⊢
    apply actual_every_cost_feasible_flow_has_the_source_constrained_reward_upper_bound gamma hg hg1 _ hflow
    have hd : 0<1-gamma := sub_pos.mpr hg1
    convert (div_le_iff₀ hd).1 hcost using 1 <;> simp only [pathOccupancy,mul_comm]

theorem actual_constrained_optimum_strictly_exceeds_resting_and_requires_nonpure_source_flow
    (gamma : ℝ) (hg : 9/11<gamma) (hg1 : gamma<1) :
    1/(1-gamma)<optimalReturn gamma ∧ 0<optimalFlow gamma 0 0 ∧
      0<optimalFlow gamma 0 1 ∧
      (optimalFlow gamma 0 0+optimalFlow gamma 0 1)≠0 := by
  have hg0 : 0<gamma := by linarith
  have hd : 0<1-gamma := sub_pos.mpr hg1
  have hcoeff : 0<2-1/gamma := by
    rw [sub_pos,div_lt_iff₀ hg0]
    linarith
  have hfirst : 0<1-(9/2)*(1-gamma)/gamma := by
    rw [sub_pos,div_lt_iff₀ hg0]
    linarith
  have hsecond : 0<(9/2:ℝ)*(1-gamma)^2/gamma := by positivity
  constructor
  · unfold optimalReturn
    apply (div_lt_div_iff_of_pos_right hd).2
    have hm : 0<(2-1/gamma)*(9/2)*(1-gamma) := by positivity
    linarith
  norm_num [optimalFlow]
  exact ⟨sub_pos.mp hfirst,hsecond,by linarith⟩

theorem actual_source_point_nine_constrained_value_and_flow :
    optimalReturn (9/10)=14 ∧
      optimalFlow (9/10)=(!![1/2,1/20;0,9/20] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      IsGreatest {v : ℝ | ∃ pi : HistoryPolicy (Fin 2) (Fin 2),
        pathReturn (model 0) (9/10) pi actualHarvestCost≤9/2 ∧
        pathReturn (model 0) (9/10) pi (harvestReward 2)=v} (14:ℝ) := by
  have hv : optimalReturn (9/10)=14 := by norm_num [optimalReturn]
  refine ⟨hv,?_,?_⟩
  · ext s a
    fin_cases s <;> fin_cases a <;> norm_num [optimalFlow]
  · rw [←hv]
    exact actual_all_history_constrained_optimum_is_attained_by_a_constructed_stationary_path (9/10) (by norm_num) (by norm_num)

end SafeLearning.CompleteAppliedHarvestConstrained
