import SafeLearning.CompleteAppliedBandit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SafeLearning.CompleteModulesLandscapeRareSpike
open CompleteAppliedProbability CompleteAppliedBandit

def peakLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(49/50:ℝ≥0),1/50] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])
def sourcePeak : Fin 2 → ℝ := ![59,109]
def sourceCDF (level : ℝ) : ℝ := peakLaw.toMeasure.real {i | sourcePeak i ≤ level}
def sourceVaR : ℝ := sInf {level | (19/20:ℝ) ≤ sourceCDF level}

theorem actual_peak_expectation_formula (value : Fin 2 → ℝ) :
    finiteExpectation peakLaw value=(49/50:ℝ)*value 0+(1/50)*value 1 := by
  norm_num [finiteExpectation,peakLaw,Fin.sum_univ_succ]

theorem actual_source_peak_atom_probabilities :
    peakLaw.toMeasure.real {i | sourcePeak i=59}=49/50 ∧
    peakLaw.toMeasure.real {i | sourcePeak i=109}=1/50 := by
  have h0 : {i | sourcePeak i=59}=({0}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [sourcePeak]
  have h1 : {i | sourcePeak i=109}=({1}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [sourcePeak]
  rw [h0,h1]
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (0:Fin 2)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
  norm_num [peakLaw]

theorem actual_source_mean_and_overheating_probability :
    (∫ i,sourcePeak i ∂peakLaw.toMeasure)=60 ∧
    peakLaw.toMeasure.real {i | (60:ℝ)<sourcePeak i}=1/50 := by
  constructor
  · rw [←finite_expectation_is_actual_integral,actual_peak_expectation_formula]
    norm_num [sourcePeak]
  · have h : {i | (60:ℝ)<sourcePeak i}=({1}:Set (Fin 2)) := by
      ext i;fin_cases i <;> norm_num [sourcePeak]
    rw [h]
    unfold Measure.real
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
    norm_num [peakLaw]

theorem actual_source_cdf (level : ℝ) :
    sourceCDF level=if level<59 then 0 else if level<109 then 49/50 else 1 := by
  classical
  have hm : MeasurableSet {i | sourcePeak i ≤ level} :=
    measurableSet_Iic.preimage (measurable_of_finite sourcePeak)
  unfold sourceCDF Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  by_cases h59 : level<59
  · have h109 : ¬(109:ℝ) ≤ level := by linarith
    simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,peakLaw,sourcePeak,
      Fin.sum_univ_succ,Set.indicator,h59,not_le.mpr h59,h109]
  · by_cases h109 : level<109
    · simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,peakLaw,sourcePeak,
        Fin.sum_univ_succ,Set.indicator,h59,le_of_not_gt h59,h109,not_le.mpr h109]
    · norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,peakLaw,sourcePeak,
        Fin.sum_univ_succ,Set.indicator,h59,le_of_not_gt h59,h109,le_of_not_gt h109]
      simp (disch := finiteness) only [ENNReal.toReal_add]
      norm_num

theorem actual_source_ninety_five_percent_quantile : sourceVaR=59 := by
  have hs : {level | (19/20:ℝ) ≤ sourceCDF level}=Ici 59 := by
    ext level
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_source_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  simp only [sourceVaR,hs,csInf_Ici]

def tailMass (selector : Fin 2 → ℝ) : ℝ := finiteExpectation peakLaw selector
def tailCost (selector : Fin 2 → ℝ) : ℝ :=
  finiteExpectation peakLaw (fun i => selector i*sourcePeak i)
def tailMean (selector : Fin 2 → ℝ) : ℝ := tailCost selector/tailMass selector
def sourceWorstTail : Fin 2 → ℝ := ![3/98,1]

theorem actual_source_fractional_tail_mass_and_mean :
    (∀ i,sourceWorstTail i∈Icc (0:ℝ) 1) ∧
    (49/50:ℝ)*sourceWorstTail 0=3/100 ∧ (1/50:ℝ)*sourceWorstTail 1=1/50 ∧
    tailMass sourceWorstTail=1/20 ∧ tailCost sourceWorstTail=79/20 ∧
    tailMean sourceWorstTail=79 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [sourceWorstTail]
  all_goals norm_num [sourceWorstTail,tailMass,tailCost,tailMean,actual_peak_expectation_formula,sourcePeak]

theorem actual_every_admissible_worst_five_percent_selection_has_mean_at_most_seventy_nine
    (selector : Fin 2 → ℝ) (hs : ∀ i,selector i∈Icc (0:ℝ) 1)
    (hm : tailMass selector=1/20) : tailMean selector ≤ 79 := by
  have hmass : (49/50:ℝ)*selector 0+(1/50)*selector 1=1/20 := by
    simpa only [tailMass,actual_peak_expectation_formula] using hm
  have he : tailCost selector=(49/50)*59*selector 0+(1/50)*109*selector 1 := by
    norm_num [tailCost,actual_peak_expectation_formula,sourcePeak];ring
  rw [tailMean,hm,div_le_iff₀ (by norm_num)]
  rw [he]
  linarith [(hs 1).2]

theorem actual_source_tail_cvar_is_genuinely_greatest :
    IsGreatest {value : ℝ | ∃ selector : Fin 2 → ℝ,
      (∀ i,selector i∈Icc (0:ℝ) 1) ∧ tailMass selector=1/20 ∧ value=tailMean selector} 79 := by
  refine ⟨⟨sourceWorstTail,actual_source_fractional_tail_mass_and_mean.1,
    actual_source_fractional_tail_mass_and_mean.2.2.2.1,
    actual_source_fractional_tail_mass_and_mean.2.2.2.2.2.symm⟩,?_⟩
  rintro value ⟨selector,hs,hm,rfl⟩
  exact actual_every_admissible_worst_five_percent_selection_has_mean_at_most_seventy_nine selector hs hm

def sourceRiskObjective (threshold : ℝ) : ℝ :=
  threshold+20*(∫ i,max (sourcePeak i-threshold) 0 ∂peakLaw.toMeasure)

theorem actual_variational_cvar_has_global_minimum_seventy_nine (threshold : ℝ) :
    sourceRiskObjective 59=79 ∧ 79 ≤ sourceRiskObjective threshold := by
  have he (level : ℝ) : sourceRiskObjective level=level+(98/5)*max (59-level) 0+(2/5)*max (109-level) 0 := by
    rw [sourceRiskObjective,←finite_expectation_is_actual_integral,actual_peak_expectation_formula]
    simp [sourcePeak];ring
  refine ⟨by norm_num [he],?_⟩
  rw [he]
  by_cases h : threshold ≤ 59
  · linarith [le_max_left (59-threshold) 0,le_max_left (109-threshold) 0]
  · linarith [le_max_right (59-threshold) 0,le_max_left (109-threshold) 0]

theorem actual_source_variational_value_is_least : IsLeast (Set.range sourceRiskObjective) 79 := by
  refine ⟨⟨59,(actual_variational_cvar_has_global_minimum_seventy_nine 59).1⟩,?_⟩
  rintro value ⟨threshold,rfl⟩
  exact (actual_variational_cvar_has_global_minimum_seventy_nine threshold).2

theorem actual_conditioning_only_above_the_ordinary_atom_returns_the_wrong_average :
    (∫ i,sourcePeak i ∂ProbabilityTheory.cond peakLaw.toMeasure {i | (59:ℝ)<sourcePeak i})=109 ∧
    (109:ℝ)≠79 := by
  classical
  let event : Set (Fin 2) := {i | (59:ℝ)<sourcePeak i}
  have hm : MeasurableSet event := event.to_countable.measurableSet
  have he : event=({1}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [event,sourcePeak]
  have hmass : peakLaw.toMeasure event=(1/50:ℝ≥0∞) := by
    rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
    norm_num [peakLaw]
  refine ⟨?_,by norm_num⟩
  change (∫ i,sourcePeak i ∂ProbabilityTheory.cond peakLaw.toMeasure event)=109
  unfold ProbabilityTheory.cond
  rw [hmass,integral_smul_measure,←integral_indicator hm,←finite_expectation_is_actual_integral]
  norm_num [actual_peak_expectation_formula,event,sourcePeak,Set.indicator]

theorem actual_source_three_caps_have_different_verdicts :
    (∫ i,sourcePeak i ∂peakLaw.toMeasure) ≤ (60:ℝ) ∧
    ¬peakLaw.toMeasure.real {i | (60:ℝ)<sourcePeak i} ≤ (0.01:ℝ) ∧
    ¬tailMean sourceWorstTail ≤ (75:ℝ) := by
  rw [actual_source_mean_and_overheating_probability.1,
    actual_source_mean_and_overheating_probability.2,
    actual_source_fractional_tail_mass_and_mean.2.2.2.2.2]
  norm_num

end SafeLearning.CompleteModulesLandscapeRareSpike
