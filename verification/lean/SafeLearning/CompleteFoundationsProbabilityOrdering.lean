import SafeLearning.CompleteFoundationsIndependentTrials

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsProbabilityOrdering
open CompleteFoundationsIndependentTrials

theorem actual_all_times_safety_probability_bound_implies_every_time_bound
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (safe : I → Set Ω) (delta : ℝ)
    (hall : 1 - delta ≤ P.real (⋂ i, safe i)) :
    ∀ i, 1 - delta ≤ P.real (safe i) := by
  intro i
  exact hall.trans (measureReal_mono (iInter_subset safe i))

theorem actual_any_finite_horizon_failure_probability_has_the_true_union_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (horizon : ℕ) (safe : Fin (horizon + 1) → Set Ω)
    (delta : Fin (horizon + 1) → ℝ)
    (heach : ∀ t, P.real (safe t)ᶜ ≤ delta t) :
    P.real (⋃ t, (safe t)ᶜ) ≤ ∑ t, delta t := by
  exact (measureReal_iUnion_fintype_le (fun t => (safe t)ᶜ)).trans
    (Finset.sum_le_sum (fun t _ => heach t))

def counterexampleLaw : Measure (Fin 20) := (PMF.uniformOfFintype (Fin 20)).toMeasure

instance counterexampleLaw_probability : IsProbabilityMeasure counterexampleLaw := by
  unfold counterexampleLaw
  infer_instance

def counterexampleSafety (t : Fin 20) : Set (Fin 20) := {t}ᶜ

theorem actual_every_counterexample_stage_is_safe_with_probability_point_ninety_five :
    ∀ t, counterexampleLaw.real (counterexampleSafety t) = (19 / 20 : ℝ) := by
  intro t
  rw [counterexampleSafety, probReal_compl_eq_one_sub (measurableSet_singleton t)]
  have hs : counterexampleLaw.real {t} = (1 / 20 : ℝ) := by
    rw [measureReal_def, counterexampleLaw,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
  rw [hs]
  norm_num

theorem actual_counterexample_all_stage_safe_event_is_empty_and_has_probability_zero :
    (⋂ t, counterexampleSafety t) = ∅ ∧
      counterexampleLaw.real (⋂ t, counterexampleSafety t) = 0 := by
  have he : (⋂ t, counterexampleSafety t) = ∅ := by
    ext omega
    simp only [mem_iInter, counterexampleSafety, mem_compl_iff, mem_singleton_iff,
      mem_empty_iff_false, iff_false]
    intro h
    exact h omega rfl
  exact ⟨he, by rw [he]; simp⟩

theorem actual_every_time_probability_does_not_imply_the_same_all_time_probability :
    (∀ t, (19 / 20 : ℝ) ≤ counterexampleLaw.real (counterexampleSafety t)) ∧
      ¬((19 / 20 : ℝ) ≤ counterexampleLaw.real (⋂ t, counterexampleSafety t)) := by
  constructor
  · intro t
    rw [actual_every_counterexample_stage_is_safe_with_probability_point_ninety_five t]
  · rw [actual_counterexample_all_stage_safe_event_is_empty_and_has_probability_zero.2]
    norm_num

theorem actual_twenty_independent_five_percent_failures_give_the_true_all_safe_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : Fin 20 → Set Ω) (hm : ∀ t, MeasurableSet (failure t))
    (hi : iIndepSet failure P) (hp : ∀ t, P.real (failure t) = (1 / 20 : ℝ)) :
    P.real (⋂ t, (failure t)ᶜ) = (19 / 20 : ℝ) ^ 20 ∧
      |P.real (⋂ t, (failure t)ᶜ) - (358 / 1000 : ℝ)| < 1 / 2000 ∧
      P.real (⋂ t, (failure t)ᶜ) < 19 / 20 := by
  have he := (actual_independent_events_have_the_true_all_miss_probability_and_exponential_bound
    P 20 failure (1 / 20) hm hi (by norm_num) hp).1
  have hid : (1 : ℝ) - 1 / 20 = 19 / 20 := by norm_num
  rw [hid] at he
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    norm_num
  · rw [he]
    norm_num

end SafeLearning.CompleteFoundationsProbabilityOrdering
