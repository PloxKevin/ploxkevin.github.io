import SafeLearning.CompleteAppliedTailRiskSlopes
import SafeLearning.CompleteAppliedTwoAtomRisk
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTailRiskOptima
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open SafeLearning.CompleteAppliedTailRisk SafeLearning.CompleteAppliedTwoAtomRisk

/-- The upper-tail statistic is the actual supremum over fractional selections of beta mass. -/
def admissibleTailMeans {n : ℕ} (law : PMF (Fin n)) (cost : Fin n → ℝ) (beta : ℝ) : Set ℝ :=
  {value | ∃ selector : Fin n → ℝ,(∀ i,selector i ∈ Set.Icc (0:ℝ) 1) ∧
    finiteExpectation law selector=beta ∧
    value=finiteExpectation law (fun i => selector i*cost i)/beta}
def upperTailCVaR {n : ℕ} (law : PMF (Fin n)) (cost : Fin n → ℝ) (alpha : ℝ) : ℝ :=
  sSup (admissibleTailMeans law cost (1-alpha))

theorem actual_tail_average_integrals {n : ℕ} (law : PMF (Fin n))
    (cost selector : Fin n → ℝ) (beta : ℝ) :
    finiteExpectation law selector=(∫ i,selector i ∂law.toMeasure) ∧
    finiteExpectation law (fun i => selector i*cost i)/beta=
      (∫ i,selector i*cost i ∂law.toMeasure)/beta := by
  simp only [finite_expectation_is_actual_integral,and_self]

theorem actual_three_atom_cvar : upperTailCVaR lossLaw lossValue (9/10)=55 := by
  have hmass := split_tail_actual_mass_and_moments.2.1
  have hcost := split_tail_actual_mass_and_moments.2.2.1
  have hmem : (55:ℝ) ∈ admissibleTailMeans lossLaw lossValue (1-9/10) := by
    refine ⟨splitTailSelector,split_tail_actual_mass_and_moments.1,?_,?_⟩
    · convert hmass using 1 <;> norm_num [tailMass,selectedMass]
    · change (55:ℝ)=tailLoss splitTailSelector/(1-9/10)
      rw [hcost];norm_num
  have hupper : ∀ value ∈ admissibleTailMeans lossLaw lossValue (1-9/10),value≤55 := by
    rintro value ⟨selector,hsel,hm,he⟩
    have hm' : tailMass selector=1/10 := by norm_num at hm;exact hm
    have ht := (split_tail_is_genuinely_worst selector hsel hm').2
    unfold tailMean at ht
    rw [hm'] at ht
    rw [he]
    convert ht using 1 <;> norm_num [tailLoss]
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hupper) (le_csSup ⟨_,hupper⟩ hmem)

theorem actual_p7_cvar : upperTailCVaR (costLaw p7LawParameter) (costValue 10) (9/10)=10 := by
  have hmass := p7_actual_worst_tail.2.1
  have hcost := p7_actual_worst_tail.2.2.1
  have hmem : (10:ℝ) ∈ admissibleTailMeans (costLaw p7LawParameter) (costValue 10) (1-9/10) := by
    refine ⟨p7Tail,p7_actual_worst_tail.1,?_,?_⟩
    · convert hmass using 1 <;> norm_num [tailMass,selectedMass]
    · change (10:ℝ)=selectedCost p7LawParameter 10 p7Tail/(1-9/10)
      rw [hcost];norm_num
  have hupper : ∀ value ∈ admissibleTailMeans (costLaw p7LawParameter) (costValue 10) (1-9/10),
      value≤10 := by
    rintro value ⟨selector,hsel,hm,he⟩
    have hm' : selectedMass p7LawParameter selector=1/10 := by norm_num at hm;exact hm
    have ht := p7_actual_worst_tail.2.2.2.2 selector hsel hm'
    unfold selectedMean at ht
    rw [hm'] at ht
    rw [he]
    convert ht using 1 <;> norm_num [selectedCost]
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hupper) (le_csSup ⟨_,hupper⟩ hmem)

theorem actual_p11_cvar : upperTailCVaR (costLaw p11LawParameter) (costValue 100) (19/20)=20 := by
  have hmass := p11_actual_worst_tail.2.1
  have hcost := p11_actual_worst_tail.2.2.1
  have hmem : (20:ℝ) ∈ admissibleTailMeans (costLaw p11LawParameter) (costValue 100) (1-19/20) := by
    refine ⟨p11Tail,p11_actual_worst_tail.1,?_,?_⟩
    · convert hmass using 1 <;> norm_num [tailMass,selectedMass]
    · change (20:ℝ)=selectedCost p11LawParameter 100 p11Tail/(1-19/20)
      rw [hcost];norm_num
  have hupper : ∀ value ∈ admissibleTailMeans (costLaw p11LawParameter) (costValue 100) (1-19/20),
      value≤20 := by
    rintro value ⟨selector,hsel,hm,he⟩
    have hm' : selectedMass p11LawParameter selector=1/20 := by norm_num at hm;exact hm
    have ht := p11_actual_worst_tail.2.2.2.2 selector hsel hm'
    unfold selectedMean at ht
    rw [hm'] at ht
    rw [he]
    convert ht using 1 <;> norm_num [selectedCost]
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hupper) (le_csSup ⟨_,hupper⟩ hmem)

theorem actual_three_atom_variational_identity (nu : ℝ) :
    upperTailCVaR lossLaw lossValue (9/10)=excessObjective 10 ∧
      upperTailCVaR lossLaw lossValue (9/10)≤excessObjective nu := by
  rw [actual_three_atom_cvar]
  have h := actual_global_minimum_at_kink nu
  exact ⟨h.1.symm,by simpa only [h.1] using h.2.1⟩

theorem actual_p7_variational_identity (nu : ℝ) :
    upperTailCVaR (costLaw p7LawParameter) (costValue 10) (9/10)=
      riskObjective p7LawParameter 10 (1/10) 10 ∧
    upperTailCVaR (costLaw p7LawParameter) (costValue 10) (9/10)≤
      riskObjective p7LawParameter 10 (1/10) nu := by
  rw [actual_p7_cvar]
  have h := p7_actual_risk_global_minimum nu
  exact ⟨h.1.symm,by simpa only [h.1] using h.2.1⟩

theorem actual_p11_variational_identity (nu : ℝ) :
    upperTailCVaR (costLaw p11LawParameter) (costValue 100) (19/20)=
      riskObjective p11LawParameter 100 (1/20) 0 ∧
    upperTailCVaR (costLaw p11LawParameter) (costValue 100) (19/20)≤
      riskObjective p11LawParameter 100 (1/20) nu := by
  rw [actual_p11_cvar]
  have h := p11_actual_risk_global_minimum nu
  exact ⟨h.1.symm,by simpa only [h.1] using h.2.1⟩


theorem actual_probability_beyond_quantile :
    lossLaw.toMeasure.real {i | (10:ℝ)<lossValue i}=1/20 := by
  rw [SafeLearning.CompleteAppliedTailRiskSlopes.actual_tail_probability]
  rw [actual_cdf_at_atoms.2.1]
  norm_num

theorem actual_objective_strictly_decreases_before_kink :
    StrictAntiOn excessObjective (Set.Iic 10) := by
  intro x hx y hy hxy
  change x≤10 at hx
  change y≤10 at hy
  rw [actual_excess_objective_piecewise,actual_excess_objective_piecewise]
  split_ifs <;> linarith

theorem actual_objective_strictly_increases_after_kink :
    StrictMonoOn excessObjective (Set.Ici 10) := by
  intro x hx y hy hxy
  change (10:ℝ)≤x at hx
  change (10:ℝ)≤y at hy
  rw [actual_excess_objective_piecewise,actual_excess_objective_piecewise]
  split_ifs <;> linarith

theorem actual_means_differ_from_cvar :
    (∫ i,lossValue i ∂lossLaw.toMeasure)=13/2 ∧
    (∫ i,lossValue i ∂ProbabilityTheory.cond lossLaw.toMeasure {i | (10:ℝ)≤lossValue i})=65/2 ∧
    (∫ i,lossValue i ∂lossLaw.toMeasure)<upperTailCVaR lossLaw lossValue (9/10) ∧
    (∫ i,lossValue i ∂ProbabilityTheory.cond lossLaw.toMeasure {i | (10:ℝ)≤lossValue i})<
      upperTailCVaR lossLaw lossValue (9/10) := by
  have hmean : (∫ i,lossValue i ∂lossLaw.toMeasure)=13/2 := by
    rw [← finite_expectation_is_actual_integral]
    exact split_tail_actual_mass_and_moments.2.2.2.2
  rw [hmean,actual_full_atom_conditional_mean.2,actual_three_atom_cvar]
  norm_num

end SafeLearning.CompleteAppliedTailRiskOptima
