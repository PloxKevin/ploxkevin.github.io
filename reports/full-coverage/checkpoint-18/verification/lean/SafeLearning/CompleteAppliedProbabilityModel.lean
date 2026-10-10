import SafeLearning.CompleteAppliedProbability
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedProbabilityModel
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability
open scoped ENNReal NNReal

theorem independent_batch_failure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (A : Fin n → Set Ω) (q : ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hq : ∀ i, μ.real (A i)=q) : μ.real (⋃ i, A i)=1-(1-q)^n := by
  have hprod := (iIndepSet_iff A μ).mp hind Finset.univ
    (f := fun i => (A i)ᶜ) (fun i _ =>
      (MeasurableSpace.measurableSet_generateFrom (by simp : A i ∈ ({A i} : Set (Set Ω)))).compl)
  have hp : μ (⋂ i, (A i)ᶜ)=∏ i, μ (A i)ᶜ := by simpa using hprod
  have hpr : μ.real (⋂ i, (A i)ᶜ)=(1-q)^n := by
    have hh := congrArg ENNReal.toReal hp
    simp only [ENNReal.toReal_prod] at hh
    change μ.real (⋂ i, (A i)ᶜ)=_ at hh
    simp_rw [← measureReal_def,complement_probability μ _ (hA _),hq] at hh
    simpa using hh
  have hunion : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have hcomp := complement_probability μ (⋃ i, A i) hunion
  rw [Set.compl_iUnion] at hcomp
  linarith

theorem largest_independent_failure_rate (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    1-(1-q)^50 ≤ (1/50:ℝ) ↔
      q ≤ 1-(49/50:ℝ)^((50:ℝ)⁻¹) := by
  have hbase : 0 ≤ 1-q := by linarith [hq.2]
  have hpow := Real.rpow_le_rpow_iff (by norm_num : 0 ≤ (49/50:ℝ))
    (pow_nonneg hbase 50) (by norm_num : 0 < ((50:ℝ)⁻¹))
  have hroot : ((1-q)^(50:ℕ))^((50:ℝ)⁻¹)=1-q := by
    simpa using Real.pow_rpow_inv_natCast hbase (by norm_num : (50:ℕ)≠0)
  rw [hroot] at hpow
  constructor
  · intro h
    have hh : (49/50:ℝ) ≤ (1-q)^50 := by linarith
    have := hpow.mpr hh
    linarith
  · intro h
    have hh : (49/50:ℝ)^((50:ℝ)⁻¹) ≤ 1-q := by linarith
    have := hpow.mp hh
    linarith

theorem original_batch_rounding :
    |(1-(1-(1/250:ℝ))^50)-(18160/100000)| ≤ 1/200000 := by norm_num

theorem largest_rate_rounding :
    |(1-(49/50:ℝ)^((50:ℝ)⁻¹))-(403973/1000000000)| ≤ 1/2000000000 := by
  have hlo := (largest_independent_failure_rate (807945/2000000000) (by norm_num)).mp
    (by norm_num : 1-(1-(807945/2000000000:ℝ))^50 ≤ 1/50)
  have hbad : ¬ 1-(1-(807947/2000000000:ℝ))^50 ≤ 1/50 := by norm_num
  have hhi : 1-(49/50:ℝ)^((50:ℝ)⁻¹) < 807947/2000000000 :=
    not_le.mp (fun h => hbad ((largest_independent_failure_rate _ (by norm_num)).mpr h))
  rw [abs_le]
  constructor <;> linarith

def conditionalFiniteExpectation {n : ℕ} (law : PMF (Fin n))
    (X : Fin n → ℝ) (information : Set (Fin n)) : ℝ :=
  finiteExpectation law (information.indicator X)/eventProbability law information

def inspectCost (_i : Fin 4) : ℝ := 6

theorem conditional_conveyor_losses :
    conditionalFiniteExpectation conveyorLaw alwaysReleaseCost alarm=450/47 ∧
    conditionalFiniteExpectation conveyorLaw alwaysReleaseCost quiet=150/1109 ∧
    conditionalFiniteExpectation conveyorLaw inspectCost alarm=6 ∧
    conditionalFiniteExpectation conveyorLaw inspectCost quiet=6 ∧
    conditionalFiniteExpectation changedConveyorLaw alwaysReleaseCost alarm=150/49 ∧
    conditionalFiniteExpectation changedConveyorLaw alwaysReleaseCost quiet=150/4559 ∧
    conditionalFiniteExpectation changedConveyorLaw inspectCost alarm=6 ∧
    conditionalFiniteExpectation changedConveyorLaw inspectCost quiet=6 := by
  norm_num [conditionalFiniteExpectation,finiteExpectation,eventProbability,
    conveyorLaw,changedConveyorLaw,alwaysReleaseCost,inspectCost,alarm,quiet,faulty,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem signs_conditional_dependence :
    conditionalProbability uniformSigns {i | signValue i=0} {i | signSquared i=0}=1 ∧
    eventProbability uniformSigns {i | signValue i=0}=1/3 := by
  norm_num [conditionalProbability,eventProbability,uniformSigns,signValue,signSquared,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]

end SafeLearning.CompleteAppliedProbabilityModel
