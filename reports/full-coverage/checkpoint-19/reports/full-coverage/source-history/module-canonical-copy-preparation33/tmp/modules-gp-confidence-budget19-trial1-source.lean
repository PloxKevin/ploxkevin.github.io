import SafeLearning.CompleteFoundationsTelescopingModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPConfidenceBudget
open CompleteFoundationsTelescopingModels

def positiveRoundShare (delta : ℝ) (t : ℕ) : ℝ := delta / ((t : ℝ) * ((t : ℝ) + 1))
def firstRoundFailures {Ω : Type*} (failure : ℕ → Set Ω) (T : ℕ) : Set Ω :=
  ⋃ n ∈ Finset.range T, failure (n + 1)

theorem actual_positive_round_reciprocal_difference (t : ℕ) (ht : 1 ≤ t) :
    1 / ((t : ℝ) * ((t : ℝ) + 1)) = 1 / (t : ℝ) - 1 / ((t : ℝ) + 1) := by
  exact actual_positive_reciprocal_product_is_the_difference _ (by exact_mod_cast (show 0 < t by omega))

theorem actual_source_one_based_schedule_matches_the_summable_budget (delta : ℝ) (n : ℕ) :
    positiveRoundShare delta (n + 1) = failureShare delta n := by
  simp only [positiveRoundShare, failureShare, Nat.cast_add, Nat.cast_one]
  ring

theorem actual_first_T_source_budgets_have_the_exact_telescoping_sum (delta : ℝ) (T : ℕ) :
    (∑ n ∈ Finset.range T, positiveRoundShare delta (n + 1)) =
      delta * (1 - 1 / ((T : ℝ) + 1)) := by
  simp_rw [actual_source_one_based_schedule_matches_the_summable_budget]
  exact actual_failure_budget_partial_sum_has_the_exact_formula delta T

theorem actual_finite_failure_union_has_the_source_horizon_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ) (hd : 0 ≤ delta)
    (hbound : ∀ t, 1 ≤ t → P.real (failure t) ≤ positiveRoundShare delta t)
    (T : ℕ) :
    P.real (firstRoundFailures failure T) ≤ delta * (1 - 1 / ((T : ℝ) + 1)) ∧
      delta * (1 - 1 / ((T : ℝ) + 1)) ≤ delta := by
  constructor
  · calc
      _ ≤ ∑ n ∈ Finset.range T, P.real (failure (n + 1)) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ n ∈ Finset.range T, positiveRoundShare delta (n + 1) :=
        Finset.sum_le_sum (fun n _ => hbound (n + 1) (by omega))
      _ = _ := actual_first_T_source_budgets_have_the_exact_telescoping_sum delta T
  · have hnon : 0 ≤ delta / ((T : ℝ) + 1) := by positivity
    nlinarith [show delta * (1 - 1 / ((T : ℝ) + 1)) = delta - delta / ((T : ℝ) + 1) by ring]

theorem actual_finite_failure_unions_increase_to_the_positive_round_union
    {Ω : Type*} (failure : ℕ → Set Ω) :
    Monotone (firstRoundFailures failure) ∧
      (⋃ T, firstRoundFailures failure T) = ⋃ t ∈ Ici 1, failure t := by
  constructor
  · intro i j hij omega homega
    rcases mem_iUnion.mp homega with ⟨n, hn⟩
    rcases mem_iUnion.mp hn with ⟨hn, hm⟩
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hn) hij), hm⟩⟩
  · ext omega
    constructor
    · intro h
      rcases mem_iUnion.mp h with ⟨T,hT⟩
      rcases mem_iUnion.mp hT with ⟨n,hn⟩
      rcases mem_iUnion.mp hn with ⟨_,hm⟩
      exact mem_iUnion.mpr ⟨n+1,mem_iUnion.mpr ⟨by simp,hm⟩⟩
    · intro h
      rcases mem_iUnion.mp h with ⟨t,ht⟩
      rcases mem_iUnion.mp ht with ⟨ht,hm⟩
      have hp : t-1+1=t := by simp only [mem_Ici] at ht; omega
      exact mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨t-1,mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (by simp only [mem_Ici] at ht; omega), hp.symm ▸ hm⟩⟩⟩

theorem actual_probability_of_finite_failure_unions_tends_to_some_round_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) :
    Tendsto (fun T => P.real (firstRoundFailures failure T)) atTop
      (𝓝 (P.real (⋃ t ∈ Ici 1, failure t))) := by
  have hm := actual_finite_failure_unions_increase_to_the_positive_round_union failure
  have h := tendsto_measure_iUnion_atTop (μ := P) hm.1
  rw [hm.2] at h
  exact ENNReal.tendsto_toReal (measure_ne_top P _) |>.comp h

theorem actual_any_positive_round_failure_probability_is_at_most_the_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ) (hd : 0 ≤ delta)
    (hbound : ∀ t, 1 ≤ t → P.real (failure t) ≤ positiveRoundShare delta t) :
    P.real (⋃ t ∈ Ici 1, failure t) ≤ delta := by
  apply le_of_tendsto (actual_probability_of_finite_failure_unions_tends_to_some_round_failure P failure)
  exact Eventually.of_forall (fun T =>
    (actual_finite_failure_union_has_the_source_horizon_bound P failure delta hd hbound T).1.trans
      (actual_finite_failure_union_has_the_source_horizon_bound P failure delta hd hbound T).2)

theorem actual_constant_one_percent_budget_sum_and_uninformative_threshold (T : ℕ) :
    (∑ _n ∈ Finset.range T, (1 / 100 : ℝ)) = (T : ℝ) / 100 ∧
      (1 ≤ (T : ℝ) / 100 ↔ 100 ≤ T) := by
  constructor
  · simp [div_eq_mul_inv]
  · constructor <;> intro h <;> exact_mod_cast (by linarith : (100 : ℝ) ≤ T)

def marginalCounterexampleLaw : Measure (Fin 100) := (PMF.uniformOfFintype (Fin 100)).toMeasure
instance marginalCounterexampleLaw_probability : IsProbabilityMeasure marginalCounterexampleLaw := by
  unfold marginalCounterexampleLaw
  infer_instance

def marginalCounterexampleFailure (t : ℕ) : Set (Fin 100) := {⟨(t-1)%100, Nat.mod_lt _ (by decide)⟩}

theorem actual_every_positive_round_counterexample_failure_probability_is_one_percent (t : ℕ) :
    marginalCounterexampleLaw.real (marginalCounterexampleFailure t) = (1 / 100 : ℝ) := by
  rw [measureReal_def, marginalCounterexampleFailure, marginalCounterexampleLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

theorem actual_some_positive_round_counterexample_failure_is_certain :
    (⋃ t ∈ Ici 1, marginalCounterexampleFailure t) = univ ∧
      marginalCounterexampleLaw.real (⋃ t ∈ Ici 1, marginalCounterexampleFailure t) = 1 := by
  have he : (⋃ t ∈ Ici 1, marginalCounterexampleFailure t) = univ := by
    ext omega
    simp only [mem_univ, iff_true]
    refine mem_iUnion.mpr ⟨omega.val+1,mem_iUnion.mpr ⟨by simp,?_⟩⟩
    simp only [marginalCounterexampleFailure, mem_singleton_iff]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt omega.isLt]
  exact ⟨he,by rw [he];simp⟩

theorem actual_ninety_nine_percent_marginals_do_not_give_an_infinite_run_guarantee :
    (∀ t, marginalCounterexampleLaw.real (marginalCounterexampleFailure t)ᶜ = (99 / 100 : ℝ)) ∧
      marginalCounterexampleLaw.real (⋂ t ∈ Ici 1, (marginalCounterexampleFailure t)ᶜ) = 0 := by
  constructor
  · intro t
    rw [probReal_compl_eq_one_sub (measurableSet_singleton _),
      actual_every_positive_round_counterexample_failure_probability_is_one_percent]
    norm_num
  · have he : (⋂ t ∈ Ici 1, (marginalCounterexampleFailure t)ᶜ) =
        (⋃ t ∈ Ici 1, marginalCounterexampleFailure t)ᶜ := by
      ext omega
      simp
    rw [he,actual_some_positive_round_counterexample_failure_is_certain.1]
    simp

end SafeLearning.CompleteModulesGPConfidenceBudget
