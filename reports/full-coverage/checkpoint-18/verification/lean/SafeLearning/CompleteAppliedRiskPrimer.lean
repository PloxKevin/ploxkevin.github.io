import SafeLearning.CompleteAppliedTailRiskOptima
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedRiskPrimer
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open SafeLearning.CompleteAppliedTailRisk SafeLearning.CompleteAppliedTailRiskOptima
open scoped ENNReal NNReal

def sourceCost : Fin 3 → ℝ := ![0,2,10]
def sourceCDF (z : ℝ) : ℝ := lossLaw.toMeasure.real {i | sourceCost i ≤ z}
def sourceVaR (alpha : ℝ) : ℝ := sInf {z | alpha ≤ sourceCDF z}

theorem actual_source_integral (X : Fin 3 → ℝ) :
    (∫ i,X i ∂lossLaw.toMeasure)=(4/5)*X 0+(3/20)*X 1+(1/20)*X 2 := by
  rw [← finite_expectation_is_actual_integral,actual_loss_expectation_formula]

theorem actual_source_CDF (z : ℝ) :
    sourceCDF z=if z<0 then 0 else if z<2 then 4/5 else if z<10 then 19/20 else 1 := by
  classical
  have hm : MeasurableSet {i | sourceCost i ≤ z} :=
    measurableSet_Iic.preimage (measurable_of_finite sourceCost)
  unfold sourceCDF Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  by_cases h0 : z<0
  · have h2 : ¬(2:ℝ) ≤ z := by linarith
    have h10 : ¬(10:ℝ) ≤ z := by linarith
    simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
      Fin.sum_univ_succ,Set.indicator,h0,not_le.mpr h0,h2,h10]
  · by_cases h2 : z<2
    · have h10 : ¬(10:ℝ) ≤ z := by linarith
      simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,sourceCost,
        Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h2,not_le.mpr h2,h10]
    · by_cases h10 : z<10
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

theorem actual_source_mean_and_positive_probability :
    (∫ i,sourceCost i ∂lossLaw.toMeasure)=4/5 ∧
    lossLaw.toMeasure.real {i | 0<sourceCost i}=1/5 := by
  constructor
  · norm_num [actual_source_integral,sourceCost]
  · have hs : {i | 0<sourceCost i}={i | sourceCost i ≤ 0}ᶜ := by
      ext i; simp
    have hm : MeasurableSet {i | sourceCost i ≤ 0} :=
      measurableSet_Iic.preimage (measurable_of_finite sourceCost)
    rw [hs,probReal_compl_eq_one_sub hm]
    change 1-sourceCDF 0=1/5
    norm_num [actual_source_CDF]

theorem actual_source_quantile : sourceVaR (9/10)=2 := by
  have hs : {z | (9/10:ℝ) ≤ sourceCDF z}=Set.Ici 2 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_source_CDF]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  simp only [sourceVaR,hs,csInf_Ici]

theorem actual_source_split_tail :
    (∀ i,splitTailSelector i ∈ Set.Icc (0:ℝ) 1) ∧
    (∫ i,splitTailSelector i ∂lossLaw.toMeasure)=1/10 ∧
    (∫ i,splitTailSelector i*sourceCost i ∂lossLaw.toMeasure)=3/5 := by
  refine ⟨split_tail_actual_mass_and_moments.1,?_,?_⟩
  all_goals norm_num [actual_source_integral,splitTailSelector,sourceCost]

theorem actual_source_every_tail_upper (selector : Fin 3 → ℝ)
    (hs : ∀ i,selector i ∈ Set.Icc (0:ℝ) 1)
    (hm : finiteExpectation lossLaw selector=1/10) :
    finiteExpectation lossLaw (fun i => selector i*sourceCost i)/(1/10) ≤ 6 := by
  have hm' : (4/5:ℝ)*selector 0+(3/20)*selector 1+(1/20)*selector 2=1/10 := by
    simpa only [actual_loss_expectation_formula] using hm
  have hv : finiteExpectation lossLaw (fun i => selector i*sourceCost i)=
      (3/10)*selector 1+(1/2)*selector 2 := by
    norm_num [actual_loss_expectation_formula,sourceCost]
    ring
  rw [hv]
  linarith [(hs 0).1,(hs 2).2]

theorem actual_source_fractional_CVaR : upperTailCVaR lossLaw sourceCost (9/10)=6 := by
  have hmem : (6:ℝ) ∈ admissibleTailMeans lossLaw sourceCost (1-9/10) := by
    refine ⟨splitTailSelector,actual_source_split_tail.1,?_,?_⟩
    · rw [finite_expectation_is_actual_integral,actual_source_split_tail.2.1]
      norm_num
    · rw [finite_expectation_is_actual_integral,actual_source_split_tail.2.2]
      norm_num
  have hupper : ∀ value ∈ admissibleTailMeans lossLaw sourceCost (1-9/10),value ≤ 6 := by
    rintro value ⟨selector,hs,hm,he⟩
    have hm' : finiteExpectation lossLaw selector=1/10 := by norm_num at hm;exact hm
    rw [he]
    convert actual_source_every_tail_upper selector hs hm' using 1 <;> norm_num
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hupper) (le_csSup ⟨_,hupper⟩ hmem)

def sourceRU (nu : ℝ) : ℝ := nu+10*(∫ i,max (sourceCost i-nu) 0 ∂lossLaw.toMeasure)

theorem actual_source_RU_piecewise (nu : ℝ) :
    sourceRU nu=if nu ≤ 0 then 8-9*nu else if nu ≤ 2 then 8-nu else
      if nu ≤ 10 then 5+nu/2 else nu := by
  unfold sourceRU
  rw [actual_source_integral]
  norm_num [sourceCost]
  split_ifs with h0 h2 h10
  · rw [max_eq_left (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_right (by linarith)]
    ring

theorem actual_source_RU_unique_minimum (nu : ℝ) :
    sourceRU 2=6 ∧ sourceRU 2 ≤ sourceRU nu ∧ (sourceRU nu=6 ↔ nu=2) := by
  have hk : sourceRU 2=6 := by norm_num [actual_source_RU_piecewise]
  refine ⟨hk,?_,?_⟩
  · rw [hk,actual_source_RU_piecewise];split_ifs <;> linarith
  · rw [actual_source_RU_piecewise];split_ifs <;> constructor <;> intro h <;> linarith

theorem actual_source_CVaR_RU_identity (nu : ℝ) :
    upperTailCVaR lossLaw sourceCost (9/10)=sourceRU (sourceVaR (9/10)) ∧
    upperTailCVaR lossLaw sourceCost (9/10) ≤ sourceRU nu := by
  rw [actual_source_fractional_CVaR,actual_source_quantile]
  have h:=actual_source_RU_unique_minimum nu
  exact ⟨h.1.symm,by simpa only [h.1] using h.2.1⟩

theorem actual_source_excess_at_VaR :
    (∫ i,max (sourceCost i-sourceVaR (9/10)) 0 ∂lossLaw.toMeasure)=2/5 := by
  rw [actual_source_quantile,actual_source_integral]
  norm_num [sourceCost]

theorem actual_source_variance_and_standard_deviation :
    (∫ i,(sourceCost i-(∫ j,sourceCost j ∂lossLaw.toMeasure))^2 ∂lossLaw.toMeasure)=124/25 ∧
    |Real.sqrt (124/25:ℝ)-2227/1000|<1/2000 := by
  rw [actual_source_mean_and_positive_probability.1]
  constructor
  · norm_num [actual_source_integral,sourceCost]
  · have hs:=Real.sq_sqrt (by norm_num : 0 ≤ (124/25:ℝ))
    rw [abs_lt];constructor <;> nlinarith [Real.sqrt_nonneg (124/25:ℝ)]

theorem actual_source_mean_chance_accept_tail_reject :
    (∫ i,sourceCost i ∂lossLaw.toMeasure) ≤ 1 ∧
    lossLaw.toMeasure.real {i | 0<sourceCost i} ≤ 1/4 ∧
    ¬upperTailCVaR lossLaw sourceCost (9/10) ≤ 5 := by
  rw [actual_source_mean_and_positive_probability.1,
    actual_source_mean_and_positive_probability.2,actual_source_fractional_CVaR]
  norm_num
end SafeLearning.CompleteAppliedRiskPrimer
