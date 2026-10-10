import SafeLearning.CompleteAppliedTailRisk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteModulesLandscapeTailAtom
open CompleteAppliedProbability CompleteAppliedBandit CompleteAppliedTailRisk

def sourceCost : Fin 3→ℝ := ![0,2,10]
def sourceCDF (level : ℝ) : ℝ := lossLaw.toMeasure.real {i | sourceCost i ≤ level}
def sourceVaR : ℝ := sInf {level | (9/10:ℝ) ≤ sourceCDF level}

theorem actual_source_cost_is_nonnegative (i : Fin 3) : 0 ≤ sourceCost i := by
  fin_cases i <;> norm_num [sourceCost]

theorem actual_source_expected_cost_is_four_fifths :
    (∫ i,sourceCost i ∂lossLaw.toMeasure)=4/5 := by
  rw [←finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  norm_num [sourceCost]

theorem actual_source_cost_cdf (level : ℝ) :
    sourceCDF level=if level<0 then 0 else if level<2 then 4/5 else if level<10 then 19/20 else 1 := by
  classical
  have hm : MeasurableSet {i | sourceCost i ≤ level} :=
    measurableSet_Iic.preimage (measurable_of_finite sourceCost)
  unfold sourceCDF Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  by_cases h0 : level<0
  · have h2 : ¬(2:ℝ) ≤ level := by linarith
    have h10 : ¬(10:ℝ) ≤ level := by linarith
    simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
      Fin.sum_univ_succ,Set.indicator,h0,not_le.mpr h0,h2,h10]
  · by_cases h2 : level<2
    · have h10 : ¬(10:ℝ) ≤ level := by linarith
      simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
        Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h2,not_le.mpr h2,h10]
    · by_cases h10 : level<10
      · norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
          Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h2,le_of_not_gt h2,
          h10,not_le.mpr h10]
        simp (disch := finiteness) only [ENNReal.toReal_add]
        norm_num
      · norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
          Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h2,le_of_not_gt h2,
          h10,le_of_not_gt h10]
        simp (disch := finiteness) only [ENNReal.toReal_add]
        norm_num

theorem actual_source_atom_probabilities_and_cdf_values :
    lossLaw.toMeasure.real {i | sourceCost i=0}=4/5 ∧
    lossLaw.toMeasure.real {i | sourceCost i=2}=3/20 ∧
    lossLaw.toMeasure.real {i | sourceCost i=10}=1/20 ∧
    sourceCDF 0=4/5 ∧ sourceCDF 2=19/20 := by
  have hz : {i | sourceCost i=0}=({0}:Set (Fin 3)) := by
    ext i;fin_cases i <;> norm_num [sourceCost]
  have hm : {i | sourceCost i=2}=({1}:Set (Fin 3)) := by
    ext i;fin_cases i <;> norm_num [sourceCost]
  have hh : {i | sourceCost i=10}=({2}:Set (Fin 3)) := by
    ext i;fin_cases i <;> norm_num [sourceCost]
  rw [hz,hm,hh]
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (0:Fin 3)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 3)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (2:Fin 3))]
  norm_num [lossLaw,actual_source_cost_cdf]

theorem actual_source_ninety_percent_quantile_is_two : sourceVaR=2 := by
  have hs : {level | (9/10:ℝ) ≤ sourceCDF level}=Ici 2 := by
    ext level
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_source_cost_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  simp only [sourceVaR,hs,csInf_Ici]

def sourceTailCost (selector : Fin 3→ℝ) : ℝ :=
  finiteExpectation lossLaw (fun i=>selector i*sourceCost i)
def sourceTailMean (selector : Fin 3→ℝ) : ℝ := sourceTailCost selector/tailMass selector
def sourceWorstTail : Fin 3→ℝ := ![0,1/3,1]

theorem actual_source_worst_tail_masses_cost_and_mean :
    (∀ i,sourceWorstTail i∈Icc (0:ℝ) 1) ∧ tailMass sourceWorstTail=1/10 ∧
      (3/20:ℝ)*sourceWorstTail 1=1/20 ∧ (1/20:ℝ)*sourceWorstTail 2=1/20 ∧
      sourceTailCost sourceWorstTail=3/5 ∧ sourceTailMean sourceWorstTail=6 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [sourceWorstTail]
  all_goals norm_num [tailMass,sourceTailCost,sourceTailMean,actual_loss_expectation_formula,
    sourceWorstTail,sourceCost]

theorem actual_source_fractional_tail_is_genuinely_worst (selector : Fin 3→ℝ)
    (hs : ∀ i,selector i∈Icc (0:ℝ) 1) (hm : tailMass selector=1/10) :
    sourceTailCost selector ≤ 3/5 ∧ sourceTailMean selector ≤ 6 := by
  have hmass : (4/5:ℝ)*selector 0+(3/20)*selector 1+(1/20)*selector 2=1/10 := by
    simpa only [tailMass,actual_loss_expectation_formula] using hm
  have he : sourceTailCost selector=(3/10)*selector 1+(1/2)*selector 2 := by
    norm_num [sourceTailCost,actual_loss_expectation_formula,sourceCost]
    ring
  have hb : sourceTailCost selector ≤ 3/5 := by
    rw [he]
    linarith [(hs 0).1,(hs 2).2]
  refine ⟨hb,?_⟩
  rw [sourceTailMean,hm]
  linarith

theorem actual_source_worst_tail_average_is_greatest :
    IsGreatest {value : ℝ | ∃ selector : Fin 3→ℝ,
      (∀ i,selector i∈Icc (0:ℝ) 1) ∧ tailMass selector=1/10 ∧ value=sourceTailMean selector} 6 := by
  refine ⟨⟨sourceWorstTail,actual_source_worst_tail_masses_cost_and_mean.1,
    actual_source_worst_tail_masses_cost_and_mean.2.1,
    actual_source_worst_tail_masses_cost_and_mean.2.2.2.2.2.symm⟩,?_⟩
  rintro value ⟨selector,hs,hm,rfl⟩
  exact (actual_source_fractional_tail_is_genuinely_worst selector hs hm).2

def sourceRiskObjective (threshold : ℝ) : ℝ :=
  threshold+10*(∫ i,max (sourceCost i-threshold) 0 ∂lossLaw.toMeasure)

theorem actual_source_risk_objective_is_the_true_variational_expression (threshold : ℝ) :
    sourceRiskObjective threshold=threshold+10*
      ((4/5)*max (-threshold) 0+(3/20)*max (2-threshold) 0+(1/20)*max (10-threshold) 0) := by
  rw [sourceRiskObjective,←finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  simp [sourceCost]

theorem actual_source_variational_objective_has_global_minimum_six (threshold : ℝ) :
    sourceRiskObjective 2=6 ∧ 6 ≤ sourceRiskObjective threshold := by
  refine ⟨by norm_num [actual_source_risk_objective_is_the_true_variational_expression],?_⟩
  rw [actual_source_risk_objective_is_the_true_variational_expression]
  by_cases ht : threshold ≤ 2
  · linarith [le_max_left (-threshold) 0,le_max_right (-threshold) 0,
      le_max_left (2-threshold) 0,le_max_left (10-threshold) 0]
  · linarith [le_max_right (-threshold) 0,le_max_right (2-threshold) 0,
      le_max_left (10-threshold) 0]

theorem actual_source_cvar_is_the_least_variational_value :
    IsLeast (Set.range sourceRiskObjective) 6 := by
  refine ⟨⟨2,(actual_source_variational_objective_has_global_minimum_six 2).1⟩,?_⟩
  rintro value ⟨threshold,rfl⟩
  exact (actual_source_variational_objective_has_global_minimum_six threshold).2

def sourceAllUpperAtoms : Fin 3→ℝ := ![0,1,1]

theorem actual_averaging_all_atoms_at_or_above_var_has_the_wrong_tail_size_and_mean :
    (∀ i,sourceAllUpperAtoms i=if 2 ≤ sourceCost i then 1 else 0) ∧
      tailMass sourceAllUpperAtoms=1/5 ∧ sourceTailMean sourceAllUpperAtoms=4 ∧
      sourceTailMean sourceAllUpperAtoms≠6 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [sourceAllUpperAtoms,sourceCost]
  all_goals norm_num [tailMass,sourceTailMean,sourceTailCost,actual_loss_expectation_formula,
    sourceAllUpperAtoms,sourceCost]

end SafeLearning.CompleteModulesLandscapeTailAtom
