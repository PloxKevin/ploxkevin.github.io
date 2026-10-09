import SafeLearning.CompleteAppliedBinomialModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedAlarmModel
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedProbabilityModel
open scoped ENNReal NNReal

/-- Joint outcomes: change/alarm, change/quiet, no-change/alarm, no-change/quiet. -/
def detectorLaw : PMF (Fin 4) := PMF.ofFintype
  (fun i => ((![(90/5000:ℝ≥0),10/5000,49/5000,4851/5000] : Fin 4 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])

theorem actual_finite_event_probability {n : ℕ} (law : PMF (Fin n)) (E : Set (Fin n)) :
    law.toMeasure.real E=eventProbability law E := by
  unfold Measure.real eventProbability
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite E).measurableSet]

theorem actual_conditioning_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I E : Set Ω) (hI : MeasurableSet I) :
    (cond μ I).real E=μ.real (E∩I)/μ.real I := by
  unfold Measure.real
  rw [cond_apply hI,ENNReal.toReal_mul,ENNReal.toReal_inv,Set.inter_comm]
  ring

theorem detector_actual_events :
    detectorLaw.toMeasure.real faulty=1/50 ∧
      detectorLaw.toMeasure.real alarm=139/5000 ∧
      detectorLaw.toMeasure.real (faulty∩alarm)=9/500 ∧
      detectorLaw.toMeasure.real (faultyᶜ∩alarm)=49/5000 := by
  simp only [actual_finite_event_probability]
  norm_num [eventProbability,detectorLaw,faulty,alarm,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem detector_actual_conditionals :
    (cond detectorLaw.toMeasure faulty).real alarm=9/10 ∧
      (cond detectorLaw.toMeasure faultyᶜ).real alarm=1/100 ∧
      (cond detectorLaw.toMeasure alarm).real faulty=90/139 ∧
      (cond detectorLaw.toMeasure alarm).real faultyᶜ=49/139 := by
  have hcomp : detectorLaw.toMeasure.real faultyᶜ=49/50 := by
    rw [probReal_compl_eq_one_sub (Set.toFinite faulty).measurableSet,detector_actual_events.1]
    norm_num
  simp only [actual_conditioning_formula _ _ _ (Set.toFinite _).measurableSet]
  rw [Set.inter_comm alarm faulty,Set.inter_comm alarm faultyᶜ]
  norm_num [detector_actual_events.1,detector_actual_events.2.1,
    detector_actual_events.2.2.1,detector_actual_events.2.2.2,hcomp]

/-- The posterior is forced by the stated base rate and actual conditional detection rates. -/
theorem actual_bayes_from_detector_rates {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D A : Set Ω)
    (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hprior : μ.real D=(1/50:ℝ))
    (hdetect : (cond μ D).real A=(9/10:ℝ))
    (hfalse : (cond μ Dᶜ).real A=(1/100:ℝ)) :
    μ.real A=139/5000 ∧ (cond μ A).real D=90/139 ∧
      (cond μ A).real Dᶜ=49/139 := by
  have hcomp : μ.real Dᶜ=49/50 := by
    rw [probReal_compl_eq_one_sub hD,hprior]
    norm_num
  rw [actual_conditioning_formula μ D A hD,hprior] at hdetect
  rw [actual_conditioning_formula μ Dᶜ A hD.compl,hcomp] at hfalse
  have hd : μ.real (A∩D)=9/500 := by linarith [hdetect]
  have hf : μ.real (A∩Dᶜ)=49/5000 := by linarith [hfalse]
  have he : A=(A∩D)∪(A∩Dᶜ) := by ext omega;simp
  have hdis : Disjoint (A∩D) (A∩Dᶜ) := by
    apply Set.disjoint_left.mpr
    intro omega h1 h2
    exact h2.2 h1.2
  have hs : μ.real A=μ.real (A∩D)+μ.real (A∩Dᶜ) := by
    calc
      μ.real A=μ.real ((A∩D)∪(A∩Dᶜ)) := congrArg μ.real he
      _=μ.real (A∩D)+μ.real (A∩Dᶜ) := measureReal_union hdis (hA.inter hD.compl)
  have ha : μ.real A=139/5000 := by rw [hd,hf] at hs;norm_num at hs;exact hs
  refine ⟨ha,?_,?_⟩
  · rw [actual_conditioning_formula μ A D hA,Set.inter_comm D A,hd,ha]
    norm_num
  · rw [actual_conditioning_formula μ A Dᶜ hA,Set.inter_comm Dᶜ A,hf,ha]
    norm_num

theorem source_posterior_three_decimal_rounding :
    |(90/139:ℝ)-(647/1000)|<1/2000 ∧
      ¬ |(90/139:ℝ)-(648/1000)|≤1/2000 ∧
      |(49/139:ℝ)-(1/3)|<3/100 := by norm_num

end SafeLearning.CompleteAppliedAlarmModel
