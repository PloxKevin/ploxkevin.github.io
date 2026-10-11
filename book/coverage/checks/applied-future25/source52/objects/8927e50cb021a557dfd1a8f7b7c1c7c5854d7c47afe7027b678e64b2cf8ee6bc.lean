import SafeLearning.CompleteAppliedBandit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SafeLearning.CompleteModulesLandscapeSignedCVaR
open CompleteAppliedProbability CompleteAppliedBandit

def sourceLaw : PMF (Fin 10) := PMF.ofFintype
  (fun _ => ((1/10:ℝ≥0) : ℝ≥0∞)) (by norm_cast;norm_num [Fin.sum_univ_succ])
def sourceExcursion : Fin 10→ℝ := ![-3/5,-1/2,-2/5,-3/10,-1/5,-1/10,0,1/5,1/2,3/2]

theorem actual_source_expectation_formula (value : Fin 10→ℝ) :
    finiteExpectation sourceLaw value=
      (value 0+value 1+value 2+value 3+value 4+value 5+value 6+value 7+value 8+value 9)/10 := by
  norm_num [finiteExpectation,sourceLaw,Fin.sum_univ_succ]
  ring

theorem actual_every_episode_has_the_printed_probability (i : Fin 10) :
    sourceLaw.toMeasure.real {i}=1/10 := by
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  norm_num [sourceLaw]

theorem actual_source_event_probability_formula (event : Set (Fin 10)) :
    sourceLaw.toMeasure.real event=finiteExpectation sourceLaw (event.indicator (fun _=>1)) := by
  rw [finite_expectation_is_actual_integral]
  exact (integral_indicator_one (μ:=sourceLaw.toMeasure) event.to_countable.measurableSet).symm

theorem actual_source_mean_excursion_and_crossing_probability :
    (∫ i,sourceExcursion i ∂sourceLaw.toMeasure)=1/100 ∧
    sourceLaw.toMeasure.real {i | 0<sourceExcursion i}=3/10 := by
  constructor
  · rw [←finite_expectation_is_actual_integral,actual_source_expectation_formula]
    norm_num [sourceExcursion]
  · rw [actual_source_event_probability_formula,actual_source_expectation_formula]
    norm_num [sourceExcursion,Set.indicator]

def sourceCDF (level : ℝ) : ℝ := sourceLaw.toMeasure.real {i | sourceExcursion i≤ level}
def sourceVaR (alpha : ℝ) : ℝ := sInf {level | alpha≤ sourceCDF level}

theorem actual_source_three_cdf_values :
    sourceCDF 0=7/10 ∧ sourceCDF (1/5)=4/5 ∧ sourceCDF (1/2)=9/10 := by
  norm_num [sourceCDF,actual_source_event_probability_formula,actual_source_expectation_formula,sourceExcursion,Set.indicator]

theorem actual_source_cdf_is_monotone : Monotone sourceCDF := by
  intro a b hab
  exact measureReal_mono (fun i hi=>hi.trans hab)

theorem actual_source_quartile_and_decile_quantiles :
    sourceVaR (3/4)=1/5 ∧ sourceVaR (9/10)=1/2 := by
  have h75 : {level | (3/4:ℝ)≤ sourceCDF level}=Ici (1/5) := by
    ext level
    simp only [Set.mem_setOf_eq,Set.mem_Ici]
    constructor
    · intro h
      by_contra hn
      have hl : level<(1/5:ℝ) := lt_of_not_ge hn
      have hsub : {i | sourceExcursion i≤ level}⊆{i | sourceExcursion i≤0} := by
        intro i hi
        fin_cases i <;> norm_num [sourceExcursion] at hi ⊢ <;> linarith
      have hc : sourceCDF level≤ sourceCDF 0 := measureReal_mono hsub
      rw [actual_source_three_cdf_values.1] at hc
      linarith
    · intro h
      have hc := actual_source_cdf_is_monotone h
      rw [actual_source_three_cdf_values.2.1] at hc
      linarith
  have h90 : {level | (9/10:ℝ)≤ sourceCDF level}=Ici (1/2) := by
    ext level
    simp only [Set.mem_setOf_eq,Set.mem_Ici]
    constructor
    · intro h
      by_contra hn
      have hl : level<(1/2:ℝ) := lt_of_not_ge hn
      have hsub : {i | sourceExcursion i≤ level}⊆{i | sourceExcursion i≤1/5} := by
        intro i hi
        fin_cases i <;> norm_num [sourceExcursion] at hi ⊢ <;> linarith
      have hc : sourceCDF level≤ sourceCDF (1/5) := measureReal_mono hsub
      rw [actual_source_three_cdf_values.2.1] at hc
      linarith
    · intro h
      exact (actual_source_three_cdf_values.2.2.symm.le).trans (actual_source_cdf_is_monotone h)
  simp only [sourceVaR,h75,h90,csInf_Ici,and_self]

def tailMass (selector : Fin 10→ℝ) : ℝ := finiteExpectation sourceLaw selector
def tailCost (selector : Fin 10→ℝ) : ℝ := finiteExpectation sourceLaw (fun i=>selector i*sourceExcursion i)
def tailMean (selector : Fin 10→ℝ) : ℝ := tailCost selector/tailMass selector
def tail75 : Fin 10→ℝ := ![0,0,0,0,0,0,0,1/2,1,1]
def tail90 : Fin 10→ℝ := ![0,0,0,0,0,0,0,0,0,1]

theorem actual_source_fractional_quarter_tail_and_decile_tail :
    (∀ i,tail75 i∈Icc (0:ℝ) 1) ∧
    tailMass tail75=1/4 ∧ tailCost tail75=21/100 ∧ tailMean tail75=21/25 ∧
    (1/10:ℝ)*tail75 7=1/20 ∧
    (∀ i,tail90 i∈Icc (0:ℝ) 1) ∧
    tailMass tail90=1/10 ∧ tailCost tail90=3/20 ∧ tailMean tail90=3/2 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [tail75]
  · norm_num [tailMass,actual_source_expectation_formula,tail75]
  · norm_num [tailCost,actual_source_expectation_formula,tail75,sourceExcursion]
  · norm_num [tailMean,tailCost,tailMass,actual_source_expectation_formula,tail75,sourceExcursion]
  · norm_num [tail75]
  · intro i;fin_cases i <;> norm_num [tail90]
  · norm_num [tailMass,actual_source_expectation_formula,tail90]
  · norm_num [tailCost,actual_source_expectation_formula,tail90,sourceExcursion]
  · norm_num [tailMean,tailCost,tailMass,actual_source_expectation_formula,tail90,sourceExcursion]

theorem actual_every_admissible_quarter_tail_has_average_at_most_twenty_one_twenty_fifths
    (selector : Fin 10→ℝ) (hs : ∀ i,selector i∈Icc (0:ℝ) 1)
    (hm : tailMass selector=1/4) : tailMean selector≤21/25 := by
  have hmass := hm
  rw [tailMass,actual_source_expectation_formula] at hmass
  have hcost : tailCost selector≤21/100 := by
    rw [tailCost,actual_source_expectation_formula]
    norm_num [sourceExcursion]
    linarith [(hs 0).1,(hs 1).1,(hs 2).1,(hs 3).1,(hs 4).1,(hs 5).1,(hs 6).1,(hs 8).2,(hs 9).2]
  rw [tailMean,hm,div_le_iff₀ (by norm_num)]
  linarith

theorem actual_every_admissible_decile_tail_has_average_at_most_three_halves
    (selector : Fin 10→ℝ) (hs : ∀ i,selector i∈Icc (0:ℝ) 1)
    (hm : tailMass selector=1/10) : tailMean selector≤3/2 := by
  have hmass := hm
  rw [tailMass,actual_source_expectation_formula] at hmass
  have hcost : tailCost selector≤3/20 := by
    rw [tailCost,actual_source_expectation_formula]
    norm_num [sourceExcursion]
    linarith [(hs 0).1,(hs 1).1,(hs 2).1,(hs 3).1,(hs 4).1,(hs 5).1,(hs 6).1,(hs 7).1,(hs 8).1]
  rw [tailMean,hm,div_le_iff₀ (by norm_num)]
  linarith

theorem actual_source_two_tail_cvars_are_genuinely_greatest :
    IsGreatest {value : ℝ | ∃ selector : Fin 10→ℝ,
      (∀ i,selector i∈Icc (0:ℝ) 1) ∧ tailMass selector=1/4 ∧ value=tailMean selector} (21/25) ∧
    IsGreatest {value : ℝ | ∃ selector : Fin 10→ℝ,
      (∀ i,selector i∈Icc (0:ℝ) 1) ∧ tailMass selector=1/10 ∧ value=tailMean selector} (3/2) := by
  have hs := actual_source_fractional_quarter_tail_and_decile_tail
  constructor
  · refine ⟨⟨tail75,hs.1,hs.2.1,hs.2.2.2.1.symm⟩,?_⟩
    rintro value ⟨selector,h,hmem,rfl⟩
    exact actual_every_admissible_quarter_tail_has_average_at_most_twenty_one_twenty_fifths selector h hmem
  · refine ⟨⟨tail90,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.symm⟩,?_⟩
    rintro value ⟨selector,h,hmem,rfl⟩
    exact actual_every_admissible_decile_tail_has_average_at_most_three_halves selector h hmem

def sourceRiskObjective (alpha threshold : ℝ) : ℝ :=
  threshold+(1-alpha)⁻¹*(∫ i,max (sourceExcursion i-threshold) 0 ∂sourceLaw.toMeasure)

theorem actual_source_variational_cvars_have_global_minima (threshold : ℝ) :
    sourceRiskObjective (3/4) (1/5)=21/25 ∧ 21/25≤ sourceRiskObjective (3/4) threshold ∧
    sourceRiskObjective (9/10) (1/2)=3/2 ∧ 3/2≤ sourceRiskObjective (9/10) threshold := by
  have hformula (alpha level : ℝ) : sourceRiskObjective alpha level=
      level+(1-alpha)⁻¹*(max (-3/5-level) 0+max (-1/2-level) 0+max (-2/5-level) 0+
      max (-3/10-level) 0+max (-1/5-level) 0+max (-1/10-level) 0+max (-level) 0+
      max (1/5-level) 0+max (1/2-level) 0+max (3/2-level) 0)/10 := by
    rw [sourceRiskObjective,←finite_expectation_is_actual_integral,actual_source_expectation_formula]
    simp [sourceExcursion];ring
  have h0 := le_max_right (-3/5-threshold) (0:ℝ)
  have h1 := le_max_right (-1/2-threshold) (0:ℝ)
  have h2 := le_max_right (-2/5-threshold) (0:ℝ)
  have h3 := le_max_right (-3/10-threshold) (0:ℝ)
  have h4 := le_max_right (-1/5-threshold) (0:ℝ)
  have h5 := le_max_right (-1/10-threshold) (0:ℝ)
  have h6 := le_max_right (-threshold) (0:ℝ)
  have h7 := le_max_right (1/5-threshold) (0:ℝ)
  have h8 := le_max_right (1/2-threshold) (0:ℝ)
  have h9 := le_max_right (3/2-threshold) (0:ℝ)
  have h7' := le_max_left (1/5-threshold) (0:ℝ)
  have h8' := le_max_left (1/2-threshold) (0:ℝ)
  have h9' := le_max_left (3/2-threshold) (0:ℝ)
  refine ⟨by norm_num [hformula],?_,by norm_num [hformula],?_⟩
  · rw [hformula];norm_num;linarith
  · rw [hformula];norm_num;linarith

theorem actual_source_two_variational_cvars_are_least :
    IsLeast (Set.range (sourceRiskObjective (3/4))) (21/25) ∧
    IsLeast (Set.range (sourceRiskObjective (9/10))) (3/2) := by
  constructor
  · refine ⟨⟨1/5,(actual_source_variational_cvars_have_global_minima 0).1⟩,?_⟩
    rintro value ⟨threshold,rfl⟩
    exact (actual_source_variational_cvars_have_global_minima threshold).2.1
  · refine ⟨⟨1/2,(actual_source_variational_cvars_have_global_minima 0).2.2.1⟩,?_⟩
    rintro value ⟨threshold,rfl⟩
    exact (actual_source_variational_cvars_have_global_minima threshold).2.2.2

theorem actual_source_maximum_excursion_and_safety_verdicts :
    IsGreatest (Set.range sourceExcursion) (3/2) ∧
    (∫ i,sourceExcursion i ∂sourceLaw.toMeasure)≤1/20 ∧
    ¬(∫ i,sourceExcursion i ∂sourceLaw.toMeasure)≤0 ∧
    ¬sourceLaw.toMeasure.real {i | 0<sourceExcursion i}≤1/5 ∧
    ¬tailMean tail75≤0 ∧ ¬tailMean tail90≤0 ∧ ¬(3/2:ℝ)≤0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,by norm_num⟩
  · refine ⟨⟨9,by norm_num [sourceExcursion]⟩,?_⟩
    rintro value ⟨i,rfl⟩
    fin_cases i <;> norm_num [sourceExcursion]
  · rw [actual_source_mean_excursion_and_crossing_probability.1];norm_num
  · rw [actual_source_mean_excursion_and_crossing_probability.1];norm_num
  · rw [actual_source_mean_excursion_and_crossing_probability.2];norm_num
  · rw [actual_source_fractional_quarter_tail_and_decile_tail.2.2.2.1];norm_num
  · rw [actual_source_fractional_quarter_tail_and_decile_tail.2.2.2.2.2.2.2.2];norm_num

end SafeLearning.CompleteModulesLandscapeSignedCVaR
