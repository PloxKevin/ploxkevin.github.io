import SafeLearning.CompleteAppliedBandit
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteCMDPTailRisk
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open scoped ENNReal NNReal Topology

def lossLaw : PMF (Fin 3) := PMF.ofFintype
  (fun i => ((![(9/10:ℝ≥0),2/25,1/50] : Fin 3 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])
def lossValue : Fin 3 → ℝ := ![0,10,100]
def lossCDF (z : ℝ) : ℝ := lossLaw.toMeasure.real {i | lossValue i≤z}
def lossVaR (alpha : ℝ) : ℝ := sInf {z | alpha≤lossCDF z}

theorem actual_loss_expectation_formula (X : Fin 3 → ℝ) :
    finiteExpectation lossLaw X=(9/10)*X 0+(2/25)*X 1+(1/50)*X 2 := by
  norm_num [finiteExpectation,lossLaw,Fin.sum_univ_succ]
  ring

theorem actual_loss_cdf (z : ℝ) :
    lossCDF z=if z<0 then 0 else if z<10 then 9/10 else if z<100 then 49/50 else 1 := by
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

theorem actual_cdf_at_atoms : lossCDF 0=9/10 ∧ lossCDF 10=49/50 ∧ lossCDF 100=1 := by
  norm_num [actual_loss_cdf]


theorem actual_ninety_five_percent_VaR : lossVaR (19/20)=10 := by
  have h : {z | (19/20:ℝ)≤lossCDF z}=Set.Ici 10 := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_Ici,actual_loss_cdf]
    split_ifs <;> constructor <;> intro h <;> first | linarith | norm_num at h
  simp only [lossVaR,h,csInf_Ici]

def splitTailSelector : Fin 3 → ℝ := ![0,3/8,1]
def tailMass (selector : Fin 3 → ℝ) : ℝ := finiteExpectation lossLaw selector
def tailLoss (selector : Fin 3 → ℝ) : ℝ :=
  finiteExpectation lossLaw (fun i => selector i*lossValue i)
def tailMean (selector : Fin 3 → ℝ) : ℝ := tailLoss selector/tailMass selector

theorem actual_split_tail_mass_and_loss :
    (∀ i,splitTailSelector i ∈ Set.Icc (0:ℝ) 1) ∧
    tailMass splitTailSelector=1/20 ∧ tailLoss splitTailSelector=23/10 ∧
    tailMean splitTailSelector=46 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i;fin_cases i <;> norm_num [splitTailSelector]
  all_goals norm_num [tailMass,tailLoss,tailMean,actual_loss_expectation_formula,
    splitTailSelector,lossValue]

theorem actual_split_tail_is_worst (selector : Fin 3 → ℝ)
    (hs : ∀ i,selector i ∈ Set.Icc (0:ℝ) 1)
    (hm : tailMass selector=1/20) :
    tailLoss selector≤23/10 ∧ tailMean selector≤46 := by
  have hm' : (9/10:ℝ)*selector 0+(2/25)*selector 1+(1/50)*selector 2=1/20 := by
    simpa only [tailMass,actual_loss_expectation_formula] using hm
  have hv : tailLoss selector=(4/5)*selector 1+2*selector 2 := by
    norm_num [tailLoss,actual_loss_expectation_formula,lossValue]
    ring
  have hb : tailLoss selector≤23/10 := by
    rw [hv];linarith [(hs 0).1,(hs 2).2]
  refine ⟨hb,?_⟩
  unfold tailMean
  rw [hm]
  linarith

/-- Genuine probability measure integrals, rather than assumed sample moments. -/
theorem actual_loss_mean_second_moment_and_variance :
    (∫ i,lossValue i ∂lossLaw.toMeasure)=14/5 ∧
    (∫ i,(lossValue i)^2 ∂lossLaw.toMeasure)=208 ∧
    (∫ i,(lossValue i-14/5)^2 ∂lossLaw.toMeasure)=5004/25 := by
  simp only [← finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  norm_num [lossValue]

def excessObjective (nu : ℝ) : ℝ :=
  nu+20*(∫ i,max (lossValue i-nu) 0 ∂lossLaw.toMeasure)

theorem actual_excess_objective (nu : ℝ) :
    excessObjective nu=nu+18*max (-nu) 0+(8/5)*max (10-nu) 0+
      (2/5)*max (100-nu) 0 := by
  unfold excessObjective
  rw [← finite_expectation_is_actual_integral,actual_loss_expectation_formula]
  norm_num [lossValue]
  ring

theorem actual_excess_objective_piecewise (nu : ℝ) :
    excessObjective nu=if nu≤0 then 56-19*nu else if nu≤10 then 56-nu else
      if nu≤100 then 40+3*nu/5 else nu := by
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

theorem actual_unique_global_RU_minimum (nu : ℝ) :
    excessObjective 10=46 ∧ excessObjective 10≤excessObjective nu ∧
    (excessObjective nu=excessObjective 10 ↔ nu=10) := by
  have hk : excessObjective 10=46 := by norm_num [actual_excess_objective_piecewise]
  refine ⟨hk,?_,?_⟩
  · rw [hk,actual_excess_objective_piecewise]
    split_ifs <;> linarith
  · rw [hk,actual_excess_objective_piecewise]
    split_ifs <;> constructor <;> intro h <;> linarith

theorem actual_three_printed_RU_values :
    excessObjective 0=56 ∧ excessObjective 10=46 ∧ excessObjective 100=100 := by
  norm_num [actual_excess_objective_piecewise]

end SafeLearning.CompleteCMDPTailRisk
