from pathlib import Path
r=Path('/home/oxrexkevin/SafetyBased')
p=r/'verification/lean/SafeLearning/CompleteCMDPTailRisk.lean';assert not p.exists()
s=(r/'verification/lean/SafeLearning/CompleteAppliedTailRisk.lean').read_text().split('theorem actual_loss_quantiles')[0]
s=s.replace('namespace SafeLearning.CompleteAppliedTailRisk','namespace SafeLearning.CompleteCMDPTailRisk').replace('(4/5:ℝ≥0),3/20,1/20','(9/10:ℝ≥0),2/25,1/50').replace('(4/5)*X 0+(3/20)*X 1+(1/20)*X 2','(9/10)*X 0+(2/25)*X 1+(1/50)*X 2').replace('then 4/5 else if z<100 then 19/20','then 9/10 else if z<100 then 49/50').replace('lossCDF 0=4/5 ∧ lossCDF 10=19/20','lossCDF 0=9/10 ∧ lossCDF 10=49/50')
s+=r'''
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
'''
p.write_text(s)
