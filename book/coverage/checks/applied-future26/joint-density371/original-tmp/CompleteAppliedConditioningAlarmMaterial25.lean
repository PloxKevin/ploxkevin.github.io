import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Function
namespace SafeLearning.CompleteAppliedConditioningAlarmMaterial25

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem actual_conditioning_restricts_rescales_and_retains_the_event
    (B : Set Ω) (hB : MeasurableSet B) (hp : 0 < μ.real B) :
    μ[|B] = (μ B)⁻¹ • μ.restrict B ∧ IsProbabilityMeasure μ[|B] ∧
      (∀ᵐ ω ∂μ[|B], ω ∈ B) := by
  have hn : μ B ≠ 0 := by
    intro hz
    have : μ.real B = 0 := by simp [measureReal_def, hz]
    linarith
  exact ⟨rfl, cond_isProbabilityMeasure hn, ae_cond_mem hB⟩

omit [IsProbabilityMeasure μ] in
theorem actual_conditional_probability_is_the_printed_ratio
    (A B : Set Ω) (hB : MeasurableSet B) :
    (μ[|B]).real A = μ.real (A ∩ B) / μ.real B := by
  have h := congrArg ENNReal.toReal (cond_apply hB μ A)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def,
    Set.inter_comm B A, div_eq_mul_inv, mul_comm] using h

theorem actual_conditional_probability_product_rule
    (A B : Set Ω) (hB : MeasurableSet B) :
    (μ[|B]).real A * μ.real B = μ.real (A ∩ B) := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hB A μ)
  simpa only [ENNReal.toReal_mul, ← measureReal_def, Set.inter_comm B A] using h

theorem actual_finite_partition_total_probability
    {ι : Type*} [Fintype ι] (B : ι → Set Ω)
    (hB : ∀ i, MeasurableSet (B i)) (hd : Pairwise (Disjoint on B))
    (hc : (⋃ i, B i) = univ) (A : Set Ω) (hA : MeasurableSet A) :
    μ.real A = ∑ i, (μ[|B i]).real A * μ.real (B i) := by
  have hh := measureReal_iUnion_fintype (μ:=μ)
    (f:=fun i => A ∩ B i)
    (fun i j hij => (hd hij).mono inter_subset_right inter_subset_right)
    (fun i => hA.inter (hB i))
  rw [← inter_iUnion, hc, inter_univ] at hh
  rw [hh]
  exact Finset.sum_congr rfl (fun i _ =>
    (actual_conditional_probability_product_rule μ A (B i) (hB i)).symm)

theorem actual_finite_partition_Bayes_rule
    {ι : Type*} [Fintype ι] (B : ι → Set Ω)
    (hB : ∀ i, MeasurableSet (B i)) (hd : Pairwise (Disjoint on B))
    (hc : (⋃ i, B i) = univ) (A : Set Ω) (hA : MeasurableSet A) (i : ι) :
    (μ[|A]).real (B i) = ((μ[|B i]).real A * μ.real (B i)) /
      (∑ j, (μ[|B j]).real A * μ.real (B j)) := by
  rw [actual_conditional_probability_is_the_printed_ratio μ (B i) A hA,
    inter_comm, ← actual_conditional_probability_product_rule μ A (B i) (hB i),
    ← actual_finite_partition_total_probability μ B hB hd hc A hA]

/-- Fault/alarm, fault/quiet, healthy/alarm, healthy/quiet. -/
def alarmWeights : Fin 4 → ℝ≥0 := ![19/2000, 1/2000, 99/2000, 1881/2000]
def alarmPMF : PMF (Fin 4) := PMF.ofFintype
  (fun i => (alarmWeights i : ℝ≥0∞))
  (by norm_cast; norm_num [alarmWeights, Fin.sum_univ_succ])
def alarmLaw : Measure (Fin 4) := alarmPMF.toMeasure
instance alarmProbability : IsProbabilityMeasure alarmLaw := by
  unfold alarmLaw
  infer_instance

def faulty : Set (Fin 4) := {i | i = 0 ∨ i = 1}
def alarm : Set (Fin 4) := {i | i = 0 ∨ i = 2}

private theorem actual_alarm_events :
    alarmLaw.real faulty = 1/100 ∧ alarmLaw.real alarm = 59/1000 ∧
      alarmLaw.real (faulty ∩ alarm) = 19/2000 ∧
      alarmLaw.real (faultyᶜ ∩ alarm) = 99/2000 ∧
      alarmLaw.real faultyᶜ = 99/100 := by
  norm_num [alarmLaw, alarmPMF, alarmWeights, faulty, alarm, measureReal_def,
    PMF.toMeasure_apply_fintype, Fin.sum_univ_succ, Set.indicator,
    ← ENNReal.coe_add, ENNReal.toReal_add]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem actual_normalized_alarm_experiment_has_the_source_prior_and_rates :
    alarmLaw.real faulty = 1/100 ∧
    (alarmLaw[|faulty]).real alarm = 95/100 ∧
    (alarmLaw[|faultyᶜ]).real alarm = 5/100 := by
  have h := actual_alarm_events
  rw [actual_conditional_probability_is_the_printed_ratio alarmLaw alarm faulty
    (Set.toFinite faulty).measurableSet,
    actual_conditional_probability_is_the_printed_ratio alarmLaw alarm faultyᶜ
    (Set.toFinite faultyᶜ).measurableSet,
    inter_comm alarm faulty, inter_comm alarm faultyᶜ]
  norm_num [h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

theorem actual_alarm_posterior_and_complement_are_true_conditionals :
    (alarmLaw[|alarm]).real faulty = 19/118 ∧
    (alarmLaw[|alarm]).real faultyᶜ = 99/118 := by
  have h := actual_alarm_events
  rw [actual_conditional_probability_is_the_printed_ratio alarmLaw faulty alarm
    (Set.toFinite alarm).measurableSet,
    actual_conditional_probability_is_the_printed_ratio alarmLaw faultyᶜ alarm
    (Set.toFinite alarm).measurableSet]
  norm_num [h.2.1, h.2.2.1, h.2.2.2.1]

theorem actual_alarm_posterior_printed_fraction_rounding_and_five_of_six :
    (alarmLaw[|alarm]).real faulty = (95/100:ℝ)*(1/100) /
      ((95/100)*(1/100)+(5/100)*(99/100)) ∧
    |(alarmLaw[|alarm]).real faulty - (161/1000:ℝ)| < 1/2000 ∧
    |(alarmLaw[|alarm]).real faultyᶜ - (5/6:ℝ)| < 1/100 ∧
    (alarmLaw[|alarm]).real faulty ≠ (alarmLaw[|faultyᶜ]).real alarm := by
  rw [actual_alarm_posterior_and_complement_are_true_conditionals.1,
    actual_alarm_posterior_and_complement_are_true_conditionals.2,
    actual_normalized_alarm_experiment_has_the_source_prior_and_rates.2.2]
  norm_num


def higherPriorWeights : Fin 4 → ℝ≥0 := ![19/200, 1/200, 9/200, 171/200]
def higherPriorPMF : PMF (Fin 4) := PMF.ofFintype
  (fun i => (higherPriorWeights i : ℝ≥0∞))
  (by norm_cast; norm_num [higherPriorWeights, Fin.sum_univ_succ])
def higherPriorLaw : Measure (Fin 4) := higherPriorPMF.toMeasure
instance higherPriorProbability : IsProbabilityMeasure higherPriorLaw := by
  unfold higherPriorLaw
  infer_instance

theorem actual_same_monitor_rates_with_changed_prior_give_a_different_posterior :
    higherPriorLaw.real faulty = 1/10 ∧
    (higherPriorLaw[|faulty]).real alarm = (alarmLaw[|faulty]).real alarm ∧
    (higherPriorLaw[|faultyᶜ]).real alarm = (alarmLaw[|faultyᶜ]).real alarm ∧
    (higherPriorLaw[|alarm]).real faulty = 19/28 ∧
    (higherPriorLaw[|alarm]).real faulty ≠ (alarmLaw[|alarm]).real faulty := by
  have hr := actual_normalized_alarm_experiment_has_the_source_prior_and_rates
  have hp := actual_alarm_posterior_and_complement_are_true_conditionals
  rw [actual_conditional_probability_is_the_printed_ratio higherPriorLaw alarm faulty
    (Set.toFinite faulty).measurableSet,
    actual_conditional_probability_is_the_printed_ratio higherPriorLaw alarm faultyᶜ
    (Set.toFinite faultyᶜ).measurableSet,
    actual_conditional_probability_is_the_printed_ratio higherPriorLaw faulty alarm
    (Set.toFinite alarm).measurableSet,
    hr.2.1, hr.2.2, hp.1]
  norm_num [higherPriorLaw, higherPriorPMF, higherPriorWeights, faulty, alarm,
    measureReal_def, PMF.toMeasure_apply_fintype, Fin.sum_univ_succ, Set.indicator,
    ← ENNReal.coe_add, ENNReal.toReal_add]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

end SafeLearning.CompleteAppliedConditioningAlarmMaterial25
