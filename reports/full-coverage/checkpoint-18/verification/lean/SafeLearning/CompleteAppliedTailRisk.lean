import SafeLearning.CompleteAppliedBandit
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTailRisk
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open scoped ENNReal NNReal Topology

def lossLaw : PMF (Fin 3) := PMF.ofFintype
  (fun i => ((![(4/5:ℝ≥0),3/20,1/20] : Fin 3 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])
def lossValue : Fin 3 → ℝ := ![0,10,100]
def lossCDF (z : ℝ) : ℝ := lossLaw.toMeasure.real {i | lossValue i≤z}
def lossVaR (alpha : ℝ) : ℝ := sInf {z | alpha≤lossCDF z}

theorem actual_loss_expectation_formula (X : Fin 3 → ℝ) :
    finiteExpectation lossLaw X=(4/5)*X 0+(3/20)*X 1+(1/20)*X 2 := by
  norm_num [finiteExpectation,lossLaw,Fin.sum_univ_succ]
  ring

theorem actual_loss_cdf (z : ℝ) :
    lossCDF z=if z<0 then 0 else if z<10 then 4/5 else if z<100 then 19/20 else 1 := by
  classical
  have hm : MeasurableSet {i | lossValue i≤z} :=
    measurableSet_Iic.preimage (measurable_of_finite lossValue)
  unfold lossCDF Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  by_cases h0 : z<0
  · have h10 : ¬(10:ℝ)≤z := by linarith
    have h100 : ¬(100:ℝ)≤z := by linarith
    simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,lossValue,
      Fin.sum_univ_succ,Set.indicator,h0,not_le.mpr h0,h10,h100]
  · by_cases h10 : z<10
    · have h100 : ¬(100:ℝ)≤z := by linarith
      simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,lossValue,
        Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h10,not_le.mpr h10,h100]
    · by_cases h100 : z<100
      · norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,lossValue,
          Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h10,le_of_not_gt h10,
          h100,not_le.mpr h100]
        simp (disch := finiteness) only [ENNReal.toReal_add]
        norm_num
      · norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,lossValue,
          Fin.sum_univ_succ,Set.indicator,h0,le_of_not_gt h0,h10,le_of_not_gt h10,
          h100,le_of_not_gt h100]
        simp (disch := finiteness) only [ENNReal.toReal_add]
        norm_num

theorem actual_cdf_at_atoms : lossCDF 0=4/5 ∧ lossCDF 10=19/20 ∧ lossCDF 100=1 := by
  norm_num [actual_loss_cdf]

theorem actual_loss_quantiles : lossVaR (4/5)=0 ∧ lossVaR (9/10)=10 ∧ lossVaR (19/20)=10 := by
  have h0 : {z | (4/5:ℝ)≤lossCDF z}=Set.Ici 0 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_loss_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  have h9 : {z | (9/10:ℝ)≤lossCDF z}=Set.Ici 10 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_loss_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  have h95 : {z | (19/20:ℝ)≤lossCDF z}=Set.Ici 10 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_loss_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  simp only [lossVaR,h0,h9,h95,csInf_Ici]
  trivial

def splitTailSelector : Fin 3 → ℝ := ![0,1/3,1]
def tailMass (selector : Fin 3 → ℝ) : ℝ := finiteExpectation lossLaw selector
def tailLoss (selector : Fin 3 → ℝ) : ℝ :=
  finiteExpectation lossLaw (fun i => selector i*lossValue i)
def tailMean (selector : Fin 3 → ℝ) : ℝ := tailLoss selector/tailMass selector

theorem split_tail_actual_mass_and_moments :
    (∀ i,splitTailSelector i ∈ Set.Icc (0:ℝ) 1) ∧
    tailMass splitTailSelector=1/10 ∧ tailLoss splitTailSelector=11/2 ∧
    tailMean splitTailSelector=55 ∧ finiteExpectation lossLaw lossValue=13/2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [splitTailSelector]
  all_goals norm_num [tailMass,tailLoss,tailMean,actual_loss_expectation_formula,
    splitTailSelector,lossValue]

/-- The selected mass really is the worst 10%: every admissible fractional atom selection
with that mass has no larger loss expectation or conditional mean. -/
theorem split_tail_is_genuinely_worst (selector : Fin 3 → ℝ)
    (hselector : ∀ i,selector i ∈ Set.Icc (0:ℝ) 1)
    (hmass : tailMass selector=1/10) :
    tailLoss selector≤tailLoss splitTailSelector ∧ tailMean selector≤55 := by
  have hmass' : (4/5:ℝ)*selector 0+(3/20)*selector 1+(1/20)*selector 2=1/10 := by
    simpa only [tailMass,actual_loss_expectation_formula] using hmass
  have hv : tailLoss selector=(3/2)*selector 1+5*selector 2 := by
    norm_num [tailLoss,actual_loss_expectation_formula,lossValue]
    ring
  have hbound : tailLoss selector≤11/2 := by
    rw [hv]
    linarith [(hselector 0).1,(hselector 2).2]
  constructor
  · rw [split_tail_actual_mass_and_moments.2.2.1]
    exact hbound
  · unfold tailMean
    rw [hmass]
    linarith

/-- Conditioning on the entire atom is an actual conditional-measure integral. -/
theorem actual_full_atom_conditional_mean :
    lossLaw.toMeasure.real {i | (10:ℝ)≤lossValue i}=1/5 ∧
    (∫ i,lossValue i ∂ProbabilityTheory.cond lossLaw.toMeasure {i | (10:ℝ)≤lossValue i})=65/2 := by
  classical
  let E : Set (Fin 3) := {i | (10:ℝ)≤lossValue i}
  have hm : MeasurableSet E := measurableSet_Ici.preimage (measurable_of_finite lossValue)
  have hmass : lossLaw.toMeasure E=(1/5:ℝ≥0∞) := by
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
    norm_num [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,lossLaw,lossValue,E,
      Fin.sum_univ_succ,Set.indicator]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num
  constructor
  · change (lossLaw.toMeasure E).toReal=1/5
    rw [hmass]
    norm_num
  · change (∫ i,lossValue i ∂ProbabilityTheory.cond lossLaw.toMeasure E)=65/2
    unfold ProbabilityTheory.cond
    rw [hmass,integral_smul_measure,← integral_indicator hm,
      ← finite_expectation_is_actual_integral]
    norm_num [actual_loss_expectation_formula,E,lossValue,Set.indicator]

def excessObjective (nu : ℝ) : ℝ :=
  nu+10*(∫ i,max (lossValue i-nu) 0 ∂lossLaw.toMeasure)

theorem actual_excess_objective (nu : ℝ) :
    excessObjective nu=nu+8*max (-nu) 0+(3/2)*max (10-nu) 0+
      (1/2)*max (100-nu) 0 := by
  unfold excessObjective
  rw [← finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  norm_num [lossValue]
  ring

theorem actual_excess_objective_piecewise (nu : ℝ) :
    excessObjective nu=if nu≤0 then 65-9*nu else if nu≤10 then 65-nu else
      if nu≤100 then 50+nu/2 else nu := by
  rw [actual_excess_objective]
  split_ifs with h0 h10 h100
  · rw [max_eq_left (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_right (by linarith),max_eq_right (by linarith)]
    ring

theorem actual_global_minimum_at_kink (nu : ℝ) :
    excessObjective 10=55 ∧ excessObjective 10≤excessObjective nu ∧
    (excessObjective nu=excessObjective 10 ↔ nu=10) := by
  have hk : excessObjective 10=55 := by norm_num [actual_excess_objective_piecewise]
  refine ⟨hk,?_,?_⟩
  · rw [hk,actual_excess_objective_piecewise]
    split_ifs <;> linarith
  · rw [hk,actual_excess_objective_piecewise]
    split_ifs <;> constructor <;> intro h <;> linarith

theorem actual_excess_at_minimum :
    (∫ i,max (lossValue i-10) 0 ∂lossLaw.toMeasure)=9/2 := by
  rw [← finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  norm_num [lossValue]

end SafeLearning.CompleteAppliedTailRisk
