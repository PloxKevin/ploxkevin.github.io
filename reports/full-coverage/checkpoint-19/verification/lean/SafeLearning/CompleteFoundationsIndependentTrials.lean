import SafeLearning.CompleteFoundationsExponentialLesson

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsIndependentTrials
open CompleteFoundationsExponentialLesson

theorem actual_independent_events_have_the_true_all_miss_probability_and_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (events : Fin n → Set Ω) (probability : ℝ)
    (hm : ∀ i, MeasurableSet (events i)) (hi : iIndepSet events P)
    (hp : probability ∈ Icc (0 : ℝ) 1)
    (he : ∀ i, P.real (events i) = probability) :
    P.real (⋂ i, (events i)ᶜ) = (1 - probability) ^ n ∧
      P.real (⋂ i, (events i)ᶜ) ≤ Real.exp (-probability * n) := by
  have hprod := (iIndepSet_iff events P).mp hi Finset.univ
    (f := fun i => (events i)ᶜ) (fun i _ =>
      (MeasurableSpace.measurableSet_generateFrom
        (by simp : events i ∈ ({events i} : Set (Set Ω)))).compl)
  have heq : P (⋂ i, (events i)ᶜ) = ∏ i, P (events i)ᶜ := by
    simpa using hprod
  have hr := congrArg ENNReal.toReal heq
  simp only [ENNReal.toReal_prod] at hr
  change P.real (⋂ i, (events i)ᶜ) = _ at hr
  simp_rw [← measureReal_def, probReal_compl_eq_one_sub (hm _), he] at hr
  have hmiss : P.real (⋂ i, (events i)ᶜ) = (1 - probability) ^ n := by
    simpa using hr
  refine ⟨hmiss, ?_⟩
  rw [hmiss]
  exact actual_independent_miss_probability_expression_has_exponential_upper_bound
    probability hp.1 hp.2 n

theorem actual_logarithmic_sample_budget_certifies_the_true_independent_miss_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (events : Fin n → Set Ω) (probability beta : ℝ)
    (hm : ∀ i, MeasurableSet (events i)) (hi : iIndepSet events P)
    (hp : 0 < probability) (hpu : probability ≤ 1) (hb : 0 < beta)
    (he : ∀ i, P.real (events i) = probability)
    (hn : Real.log (1 / beta) / probability ≤ (n : ℝ)) :
    P.real (⋂ i, (events i)ᶜ) ≤ beta := by
  have hmiss := actual_independent_events_have_the_true_all_miss_probability_and_exponential_bound
    P n events probability hm hi ⟨hp.le, hpu⟩ he
  have hlog := (div_le_iff₀ hp).mp hn
  have hid : Real.log (1 / beta) = -Real.log beta := by
    rw [one_div, Real.log_inv]
  rw [hid] at hlog
  have hexp : Real.exp (-probability * (n : ℝ)) ≤ beta := by
    calc
      _ ≤ Real.exp (Real.log beta) := Real.exp_le_exp.mpr (by linarith)
      _ = beta := Real.exp_log hb
  exact hmiss.2.trans hexp

theorem actual_source_three_hundred_independent_trials_miss_with_probability_point_ninety_nine_power
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (events : Fin 300 → Set Ω) (hm : ∀ i, MeasurableSet (events i))
    (hi : iIndepSet events P) (he : ∀ i, P.real (events i) = (1 / 100 : ℝ)) :
    P.real (⋂ i, (events i)ᶜ) = (99 / 100 : ℝ) ^ 300 ∧
      P.real (⋂ i, (events i)ᶜ) ≤ Real.exp (-3) := by
  have h := actual_independent_events_have_the_true_all_miss_probability_and_exponential_bound
    P 300 events (1 / 100) hm hi (by norm_num) he
  norm_num only [show (1 : ℝ) - 1 / 100 = 99 / 100 by norm_num,
    show -(1 / 100 : ℝ) * (300 : ℝ) = -3 by norm_num] at h
  exact h

end SafeLearning.CompleteFoundationsIndependentTrials
