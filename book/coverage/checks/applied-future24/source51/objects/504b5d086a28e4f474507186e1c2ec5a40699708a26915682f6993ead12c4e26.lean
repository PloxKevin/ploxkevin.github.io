import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedProbability
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- The four outcomes are faulty/alarm, faulty/quiet, sound/alarm, sound/quiet.
These are normalized PMFs, rather than four numbers without a probability law. -/
def conveyorLaw : PMF (Fin 4) := PMF.ofFintype
  (fun i => ((![(9/250:ℝ≥0),1/250,48/625,552/625] : Fin 4 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def changedConveyorLaw : PMF (Fin 4) := PMF.ofFintype
  (fun i => ((![(9/1000:ℝ≥0),1/1000,99/1250,2277/2500] : Fin 4 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])

def faulty : Set (Fin 4) := {i | i=0 ∨ i=1}
def alarm : Set (Fin 4) := {i | i=0 ∨ i=2}
def quiet : Set (Fin 4) := alarmᶜ

def eventProbability {n : ℕ} (law : PMF (Fin n)) (event : Set (Fin n)) : ℝ :=
  (law.toOuterMeasure event).toReal
def conditionalProbability {n : ℕ} (law : PMF (Fin n))
    (event information : Set (Fin n)) : ℝ :=
  eventProbability law (event ∩ information)/eventProbability law information

theorem conveyor_events :
    eventProbability conveyorLaw faulty=1/25 ∧
    eventProbability conveyorLaw alarm=141/1250 ∧
    eventProbability conveyorLaw quiet=1109/1250 ∧
    eventProbability conveyorLaw (faulty ∩ alarm)=9/250 ∧
    eventProbability conveyorLaw (faulty ∩ quiet)=1/250 := by
  norm_num [eventProbability,conveyorLaw,faulty,alarm,quiet,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator,← ENNReal.coe_add,ENNReal.toReal_add]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem conveyor_conditionals :
    conditionalProbability conveyorLaw faulty alarm=15/47 ∧
    conditionalProbability conveyorLaw faulty quiet=5/1109 ∧
    conditionalProbability conveyorLaw alarm faulty=9/10 := by
  norm_num [conditionalProbability,eventProbability,conveyorLaw,faulty,alarm,quiet,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator,← ENNReal.coe_add,ENNReal.toReal_add]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem changed_conveyor_events :
    eventProbability changedConveyorLaw alarm=441/5000 ∧
    eventProbability changedConveyorLaw quiet=4559/5000 ∧
    conditionalProbability changedConveyorLaw faulty alarm=5/49 ∧
    conditionalProbability changedConveyorLaw faulty quiet=5/4559 := by
  norm_num [conditionalProbability,eventProbability,changedConveyorLaw,faulty,alarm,quiet,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator,← ENNReal.coe_add,ENNReal.toReal_add]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

def finiteExpectation {n : ℕ} (law : PMF (Fin n)) (X : Fin n → ℝ) : ℝ :=
  ∑ i, (law i).toReal*X i

def finiteVariance {n : ℕ} (law : PMF (Fin n)) (X : Fin n → ℝ) : ℝ :=
  finiteExpectation law (fun i => (X i-finiteExpectation law X)^2)

def finiteCovariance {n : ℕ} (law : PMF (Fin n)) (X Y : Fin n → ℝ) : ℝ :=
  finiteExpectation law (fun i => (X i-finiteExpectation law X)*(Y i-finiteExpectation law Y))

def costTableLaw : PMF (Fin 3) := PMF.ofFintype
  (fun i => ((![(1/2:ℝ≥0),1/4,1/4] : Fin 3 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def costTable : Fin 3 → ℝ := ![0,2,4]

theorem cost_table_events_and_moments :
    eventProbability costTableLaw {i | 2≤costTable i}=1/2 ∧
    finiteExpectation costTableLaw costTable=3/2 ∧
    finiteExpectation costTableLaw (fun i => (costTable i)^2)=5 ∧
    finiteVariance costTableLaw costTable=11/4 ∧
    finiteExpectation costTableLaw (fun i => 3*costTable i+1)=11/2 ∧
    finiteVariance costTableLaw (fun i => 3*costTable i+1)=99/4 := by
  norm_num [eventProbability,costTableLaw,costTable,finiteExpectation,finiteVariance,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem cost_table_mean_not_outcome :
    ∀ i : Fin 3, costTable i≠finiteExpectation costTableLaw costTable := by
  intro i
  rw [cost_table_events_and_moments.2.1]
  fin_cases i <;> norm_num [costTable]

theorem cost_table_standard_deviation : Real.sqrt (11/4:ℝ)=Real.sqrt 11/2 := by
  rw [Real.sqrt_div (by norm_num)]
  norm_num

def uniformSigns : PMF (Fin 3) := PMF.ofFintype
  (fun _ => ((1/3:ℝ≥0):ℝ≥0∞)) (by norm_cast; norm_num [Fin.sum_univ_succ])
def signValue : Fin 3 → ℝ := ![-1,0,1]
def signSquared (i : Fin 3) : ℝ := (signValue i)^2

theorem signs_moments :
    finiteExpectation uniformSigns signValue=0 ∧
    finiteExpectation uniformSigns signSquared=2/3 ∧
    finiteVariance uniformSigns signValue=2/3 ∧
    finiteVariance uniformSigns signSquared=2/9 ∧
    finiteCovariance uniformSigns signValue signSquared=0 := by
  norm_num [finiteExpectation,finiteVariance,finiteCovariance,uniformSigns,
    signValue,signSquared,Fin.sum_univ_succ]

def FiniteIndependent {n : ℕ} (law : PMF (Fin n)) (X Y : Fin n → ℝ) : Prop :=
  ∀ A B : Set ℝ, eventProbability law (X ⁻¹' A ∩ Y ⁻¹' B)=
    eventProbability law (X ⁻¹' A)*eventProbability law (Y ⁻¹' B)

theorem signs_not_independent : ¬ FiniteIndependent uniformSigns signValue signSquared := by
  intro h
  have hh := h {0} {0}
  norm_num [eventProbability,uniformSigns,signValue,signSquared,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator] at hh

def fairDie : PMF (Fin 6) := PMF.ofFintype
  (fun _ => ((1/6:ℝ≥0):ℝ≥0∞)) (by norm_cast; norm_num [Fin.sum_univ_succ])
def dieEven : Set (Fin 6) := {i | (i.val+1)%2=0}
def dieAboveThree : Set (Fin 6) := {i | 3 < i.val+1}

theorem fair_die_conditioning :
    eventProbability fairDie dieEven=1/2 ∧
    eventProbability fairDie dieAboveThree=1/2 ∧
    eventProbability fairDie (dieEven ∩ dieAboveThree)=1/3 ∧
    conditionalProbability fairDie dieEven dieAboveThree=2/3 := by
  norm_num [conditionalProbability,eventProbability,fairDie,dieEven,dieAboveThree,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

open scoped Classical in
def inspectOnAlarmCost (i : Fin 4) : ℝ := if i ∈ alarm then 6 else if i ∈ faulty then 30 else 0
open scoped Classical in
def alwaysReleaseCost (i : Fin 4) : ℝ := if i ∈ faulty then 30 else 0

theorem inspection_decision_threshold (posterior : ℝ) :
    (6<30*posterior ↔ 1/5<posterior) ∧
    (6=30*posterior ↔ posterior=1/5) := by
  constructor <;> constructor <;> intro h <;> linarith

theorem conveyor_expected_costs :
    finiteExpectation conveyorLaw inspectOnAlarmCost=498/625 ∧
    finiteExpectation conveyorLaw alwaysReleaseCost=6/5 ∧
    finiteExpectation conveyorLaw (fun _ => 6)=6 ∧
    finiteExpectation conveyorLaw inspectOnAlarmCost<finiteExpectation conveyorLaw alwaysReleaseCost ∧
    finiteExpectation conveyorLaw inspectOnAlarmCost<finiteExpectation conveyorLaw (fun _ => 6) := by
  norm_num [finiteExpectation,conveyorLaw,inspectOnAlarmCost,alwaysReleaseCost,
    alarm,faulty,Fin.sum_univ_succ]

theorem conveyor_action_optimality :
    6<30*conditionalProbability conveyorLaw faulty alarm ∧
    30*conditionalProbability conveyorLaw faulty quiet<6 ∧
    30*conditionalProbability changedConveyorLaw faulty alarm<6 ∧
    30*conditionalProbability changedConveyorLaw faulty quiet<6 := by
  rw [conveyor_conditionals.1,conveyor_conditionals.2.1,
    changed_conveyor_events.2.2.1,changed_conveyor_events.2.2.2]
  norm_num

theorem changed_rule_worse :
    finiteExpectation changedConveyorLaw alwaysReleaseCost=3/10 ∧
    finiteExpectation changedConveyorLaw inspectOnAlarmCost=699/1250 ∧
    finiteExpectation changedConveyorLaw alwaysReleaseCost<
      finiteExpectation changedConveyorLaw inspectOnAlarmCost := by
  norm_num [finiteExpectation,changedConveyorLaw,inspectOnAlarmCost,alwaysReleaseCost,
    alarm,faulty,Fin.sum_univ_succ]

theorem complement_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    μ.real Aᶜ=1-μ.real A := by
  have h := measureReal_add_measureReal_compl (μ := μ) hA
  have hu : μ.real Set.univ=1 := by simp [measureReal_def]
  rw [hu] at h
  linarith

theorem finite_batch_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Fin 50 → Set Ω) (q : ℝ)
    (hq : ∀ i, μ.real (A i)≤q) : μ.real (⋃ i, A i)≤50*q := by
  calc
    μ.real (⋃ i, A i)≤∑ i, μ.real (A i) := measureReal_iUnion_fintype_le A
    _≤∑ _i : Fin 50, q := Finset.sum_le_sum fun i _ => hq i
    _=50*q := by simp

theorem batch_sufficient_bound (q : ℝ) (hq : q≤1/2500) : 50*q≤1/50 := by linarith

theorem batch_original_fails : (1/50:ℝ)<1-(1-1/250)^50 := by norm_num

/-- Genuine variance of the average of pairwise independent random variables. -/
theorem independent_average_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hInd : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (sigma2 : ℝ) (hv : ∀ i, variance (X i) μ=sigma2) :
    variance (fun w => (1/(n:ℝ))*∑ i, X i w) μ=sigma2/(n:ℝ) := by
  rw [variance_const_mul]
  have hs : variance (fun w => ∑ i, X i w) μ=∑ i, variance (X i) μ := by
    have he : (fun w => ∑ i, X i w)=(∑ i, X i) := by funext w; simp
    rw [he]
    exact IndepFun.variance_sum
      (s := Finset.univ) (X := X) (μ := μ) (fun i _ => hX i)
      (fun i _ j _ hij => hInd hij)
  rw [hs]
  simp_rw [hv]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

theorem shared_offset_average_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (offset noiseAverage : Ω → ℝ)
    (ho : MemLp offset 2 μ) (hn : MemLp noiseAverage 2 μ)
    (hInd : IndepFun offset noiseAverage μ) (n : ℕ)
    (hv : variance offset μ=2/3) (hnv : variance noiseAverage μ=1/(n:ℝ)) :
    variance (fun w => offset w+noiseAverage w) μ=2/3+1/(n:ℝ) := by
  rw [hInd.variance_fun_add ho hn,hv,hnv]

theorem shared_offset_limit :
    Tendsto (fun n : ℕ => (2/3:ℝ)+1/(n:ℝ)) atTop (𝓝 (2/3)) := by
  simpa using (tendsto_const_nhds (x := (2/3:ℝ))).add
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem shared_offset_numbers : (2/3:ℝ)+1/100=203/300 ∧
    (5/3:ℝ)/100≠203/300 ∧ (2/3:ℝ)+1=5/3 := by norm_num

theorem calibration_quadratic (theta : ℝ) :
    theta^2/4+(2-theta)^2+(-1-theta)^2/4=
      (3/2)*(theta-7/6)^2+53/24 := by ring

theorem calibration_precisions :
    (1/4:ℝ)+1+1/4=3/2 ∧ ((0:ℝ)/4+2-1/4)/(3/2)=7/6 ∧
    (1/(3/2:ℝ))=2/3 := by norm_num

/-- Correct source fractions for original C.2; the earlier ledger mapped another alarm law. -/
theorem original_c2_bayes :
    ((9/10:ℝ)*(1/50))/((9/10)*(1/50)+(1/100)*(49/50))=90/139 := by norm_num

end SafeLearning.CompleteAppliedProbability
