import SafeLearning.CompleteAppliedBandit
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTwoAtomRisk
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open scoped ENNReal NNReal

def costLaw (q : unitInterval) : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![1-(q:ℝ),(q:ℝ)] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Fin.sum_univ_zero,add_zero]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr q.2.2) q.2.1]
    simp)
def costValue (high : ℝ) : Fin 2 → ℝ := ![0,high]
def costCDF (q : unitInterval) (high z : ℝ) : ℝ :=
  (costLaw q).toMeasure.real {i | costValue high i≤z}
def costVaR (q : unitInterval) (high alpha : ℝ) : ℝ := sInf {z | alpha≤costCDF q high z}

theorem actual_two_atom_expectation (q : unitInterval) (X : Fin 2 → ℝ) :
    finiteExpectation (costLaw q) X=(1-(q:ℝ))*X 0+(q:ℝ)*X 1 := by
  unfold finiteExpectation
  simp only [costLaw,PMF.ofFintype_apply,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Fin.sum_univ_zero,add_zero]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2),ENNReal.toReal_ofReal q.2.1]

theorem actual_two_atom_mean (q : unitInterval) (high : ℝ) :
    (∫ i,costValue high i ∂(costLaw q).toMeasure)=(q:ℝ)*high := by
  rw [← finite_expectation_is_actual_integral,actual_two_atom_expectation]
  simp [costValue]

theorem actual_two_atom_cdf (q : unitInterval) (high : ℝ) (hhigh : 0<high) (z : ℝ) :
    costCDF q high z=if z<0 then 0 else if z<high then 1-(q:ℝ) else 1 := by
  classical
  have hm : MeasurableSet {i | costValue high i≤z} :=
    measurableSet_Iic.preimage (measurable_of_finite (costValue high))
  unfold costCDF Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  by_cases hz : z<0
  · have hc : ¬high≤z := by linarith
    simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,costLaw,costValue,
      Fin.sum_univ_two,Set.indicator,hz,not_le.mpr hz,hc]
  · by_cases hc : z<high
    · simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,costLaw,costValue,
        Fin.sum_univ_two,Set.indicator,hz,le_of_not_gt hz,hc,not_le.mpr hc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2)]
    · simp only [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,costLaw,PMF.ofFintype_apply,
        costValue,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.sum_univ_zero,add_zero,Set.indicator,Set.mem_setOf_eq,
        le_of_not_gt hz,le_of_not_gt hc,if_pos,if_neg,hz,hc]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr q.2.2) q.2.1]
      simp

theorem actual_low_quantile (q : unitInterval) (high alpha : ℝ) (hhigh : 0<high)
    (ha : 0<alpha) (haq : alpha≤1-(q:ℝ)) : costVaR q high alpha=0 := by
  have hs : {z | alpha≤costCDF q high z}=Set.Ici 0 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_two_atom_cdf q high hhigh]
    split_ifs <;> constructor <;> intro h <;> linarith [q.2.1]
  simp only [costVaR,hs,csInf_Ici]

theorem actual_high_quantile (q : unitInterval) (high alpha : ℝ) (hhigh : 0<high)
    (haq : 1-(q:ℝ)<alpha) (ha : alpha≤1) : costVaR q high alpha=high := by
  have hs : {z | alpha≤costCDF q high z}=Set.Ici high := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_two_atom_cdf q high hhigh]
    split_ifs <;> constructor <;> intro h <;> linarith [q.2.2]
  simp only [costVaR,hs,csInf_Ici]

def selectedMass (q : unitInterval) (selector : Fin 2 → ℝ) : ℝ :=
  finiteExpectation (costLaw q) selector
def selectedCost (q : unitInterval) (high : ℝ) (selector : Fin 2 → ℝ) : ℝ :=
  finiteExpectation (costLaw q) (fun i => selector i*costValue high i)
def selectedMean (q : unitInterval) (high : ℝ) (selector : Fin 2 → ℝ) : ℝ :=
  selectedCost q high selector/selectedMass q selector

/-- Every fractional selection of beta probability mass obeys the true worst-tail upper bound. -/
theorem actual_fractional_tail_upper (q : unitInterval) (high beta : ℝ)
    (hhigh : 0≤high) (hbeta : 0<beta) (selector : Fin 2 → ℝ)
    (hsel : ∀ i,selector i ∈ Set.Icc (0:ℝ) 1)
    (hmass : selectedMass q selector=beta) :
    selectedCost q high selector≤high*min (q:ℝ) beta ∧
      selectedMean q high selector≤high*min (q:ℝ) beta/beta := by
  have hmass' : (1-(q:ℝ))*selector 0+(q:ℝ)*selector 1=beta := by
    simpa only [selectedMass,actual_two_atom_expectation] using hmass
  have hq : (q:ℝ)*selector 1≤q := by nlinarith [(hsel 1).2,q.2.1]
  have hb : (q:ℝ)*selector 1≤beta := by
    have hn := mul_nonneg (sub_nonneg.mpr q.2.2) (hsel 0).1
    linarith
  have hm := le_min hq hb
  have hc : selectedCost q high selector=high*((q:ℝ)*selector 1) := by
    simp [selectedCost,actual_two_atom_expectation,costValue]
    ring
  have hu : selectedCost q high selector≤high*min (q:ℝ) beta := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left hm hhigh
  exact ⟨hu,by unfold selectedMean;rw [hmass];exact div_le_div_of_nonneg_right hu hbeta.le⟩

def p7LawParameter : unitInterval := ⟨1/5,by norm_num⟩
def p11LawParameter : unitInterval := ⟨1/100,by norm_num⟩
def p7Tail : Fin 2 → ℝ := ![0,1/2]
def p11Tail : Fin 2 → ℝ := ![4/99,1]

theorem p7_actual_mean_and_quantile :
    (∫ i,costValue 10 i ∂(costLaw p7LawParameter).toMeasure)=2 ∧
      costCDF p7LawParameter 10 0=4/5 ∧ costCDF p7LawParameter 10 10=1 ∧
      costVaR p7LawParameter 10 (9/10)=10 := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [actual_two_atom_mean,p7LawParameter]
  · rw [actual_two_atom_cdf p7LawParameter 10 (by norm_num)]
    norm_num [p7LawParameter]
  · rw [actual_two_atom_cdf p7LawParameter 10 (by norm_num)]
    norm_num [p7LawParameter]
  · exact actual_high_quantile p7LawParameter 10 (9/10) (by norm_num)
      (by norm_num [p7LawParameter]) (by norm_num)

theorem p7_actual_worst_tail :
    (∀ i,p7Tail i ∈ Set.Icc (0:ℝ) 1) ∧ selectedMass p7LawParameter p7Tail=1/10 ∧
    selectedCost p7LawParameter 10 p7Tail=1 ∧ selectedMean p7LawParameter 10 p7Tail=10 ∧
    ∀ selector : Fin 2 → ℝ,(∀ i,selector i ∈ Set.Icc (0:ℝ) 1) →
      selectedMass p7LawParameter selector=1/10 → selectedMean p7LawParameter 10 selector≤10 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [p7Tail]
  · norm_num [selectedMass,actual_two_atom_expectation,p7Tail,p7LawParameter]
  · norm_num [selectedCost,actual_two_atom_expectation,p7Tail,p7LawParameter,costValue]
  · norm_num [selectedMean,selectedMass,selectedCost,actual_two_atom_expectation,
      p7Tail,p7LawParameter,costValue]
  · intro selector hsel hmass
    have h := (actual_fractional_tail_upper p7LawParameter 10 (1/10) (by norm_num)
      (by norm_num) selector hsel hmass).2
    norm_num [p7LawParameter] at h
    exact h

theorem p11_actual_mean_budget_and_quantile :
    (∫ i,costValue 100 i ∂(costLaw p11LawParameter).toMeasure)=1 ∧
      (∫ i,costValue 100 i ∂(costLaw p11LawParameter).toMeasure)≤1 ∧
      costCDF p11LawParameter 100 0=99/100 ∧ costVaR p11LawParameter 100 (19/20)=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [actual_two_atom_mean,p11LawParameter]
  · norm_num [actual_two_atom_mean,p11LawParameter]
  · rw [actual_two_atom_cdf p11LawParameter 100 (by norm_num)]
    norm_num [p11LawParameter]
  · exact actual_low_quantile p11LawParameter 100 (19/20) (by norm_num)
      (by norm_num) (by norm_num [p11LawParameter])

theorem p11_actual_failure_probability :
    (costLaw p11LawParameter).toMeasure.real {i | costValue 100 i=100}=1/100 := by
  classical
  have hs : {i | costValue 100 i=100}=({1}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [costValue]
  rw [hs]
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
  norm_num [costLaw,p11LawParameter]

theorem p11_actual_worst_tail :
    (∀ i,p11Tail i ∈ Set.Icc (0:ℝ) 1) ∧ selectedMass p11LawParameter p11Tail=1/20 ∧
    selectedCost p11LawParameter 100 p11Tail=1 ∧ selectedMean p11LawParameter 100 p11Tail=20 ∧
    ∀ selector : Fin 2 → ℝ,(∀ i,selector i ∈ Set.Icc (0:ℝ) 1) →
      selectedMass p11LawParameter selector=1/20 → selectedMean p11LawParameter 100 selector≤20 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [p11Tail]
  · norm_num [selectedMass,actual_two_atom_expectation,p11Tail,p11LawParameter]
  · norm_num [selectedCost,actual_two_atom_expectation,p11Tail,p11LawParameter,costValue]
  · norm_num [selectedMean,selectedMass,selectedCost,actual_two_atom_expectation,
      p11Tail,p11LawParameter,costValue]
  · intro selector hsel hmass
    have h := (actual_fractional_tail_upper p11LawParameter 100 (1/20) (by norm_num)
      (by norm_num) selector hsel hmass).2
    norm_num [p11LawParameter] at h
    exact h

def riskObjective (q : unitInterval) (high beta nu : ℝ) : ℝ :=
  nu+(1/beta)*(∫ i,max (costValue high i-nu) 0 ∂(costLaw q).toMeasure)

theorem actual_risk_objective (q : unitInterval) (high beta nu : ℝ) :
    riskObjective q high beta nu=nu+(1/beta)*
      ((1-(q:ℝ))*max (-nu) 0+(q:ℝ)*max (high-nu) 0) := by
  unfold riskObjective
  rw [← finite_expectation_is_actual_integral,actual_two_atom_expectation]
  simp [costValue]

theorem p7_actual_risk_objective_piecewise (nu : ℝ) :
    riskObjective p7LawParameter 10 (1/10) nu=
      if nu≤0 then 20-9*nu else if nu≤10 then 20-nu else nu := by
  rw [actual_risk_objective]
  norm_num only [p7LawParameter]
  split_ifs with h0 h10
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)];ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)];ring

theorem p11_actual_risk_objective_piecewise (nu : ℝ) :
    riskObjective p11LawParameter 100 (1/20) nu=
      if nu≤0 then 20-19*nu else if nu≤100 then 20+(4/5)*nu else nu := by
  rw [actual_risk_objective]
  norm_num only [p11LawParameter]
  split_ifs with h0 h100
  · rw [max_eq_left (by linarith),max_eq_left (by linarith)];ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)];ring

theorem p7_actual_risk_global_minimum (nu : ℝ) :
    riskObjective p7LawParameter 10 (1/10) 10=10 ∧
      riskObjective p7LawParameter 10 (1/10) 10≤riskObjective p7LawParameter 10 (1/10) nu ∧
      (riskObjective p7LawParameter 10 (1/10) nu=10 ↔ nu=10) := by
  have hk : riskObjective p7LawParameter 10 (1/10) 10=10 := by
    norm_num [p7_actual_risk_objective_piecewise]
  refine ⟨hk,?_,?_⟩
  · rw [hk,p7_actual_risk_objective_piecewise];split_ifs <;> linarith
  · rw [p7_actual_risk_objective_piecewise];split_ifs <;> constructor <;> intro h <;> linarith

theorem p11_actual_risk_global_minimum (nu : ℝ) :
    riskObjective p11LawParameter 100 (1/20) 0=20 ∧
      riskObjective p11LawParameter 100 (1/20) 0≤riskObjective p11LawParameter 100 (1/20) nu ∧
      (riskObjective p11LawParameter 100 (1/20) nu=20 ↔ nu=0) := by
  have hk : riskObjective p11LawParameter 100 (1/20) 0=20 := by
    norm_num [p11_actual_risk_objective_piecewise]
  refine ⟨hk,?_,?_⟩
  · rw [hk,p11_actual_risk_objective_piecewise];split_ifs <;> linarith
  · rw [p11_actual_risk_objective_piecewise];split_ifs <;> constructor <;> intro h <;> linarith

end SafeLearning.CompleteAppliedTwoAtomRisk
