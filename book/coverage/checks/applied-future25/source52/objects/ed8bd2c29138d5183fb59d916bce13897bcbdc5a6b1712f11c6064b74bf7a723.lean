import SafeLearning.CompleteModulesGPConfidenceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace SafeLearning.CompleteModulesGPConfidenceBudgetConsequences
open CompleteModulesGPConfidenceBudget

theorem actual_per_round_probability_assumptions_force_a_nonnegative_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ)
    (hbound : ∀ t, 1 ≤ t → P.real (failure t) ≤ positiveRoundShare delta t) :
    0 ≤ delta := by
  have hb := hbound 1 (by decide)
  norm_num [positiveRoundShare] at hb
  have hp : 0 ≤ P.real (failure 1) := ENNReal.toReal_nonneg
  linarith

theorem actual_source_all_time_probability_bound_needs_no_extra_budget_domain_assumption
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ)
    (hbound : ∀ t, 1 ≤ t → P.real (failure t) ≤ positiveRoundShare delta t) :
    P.real (⋃ t ∈ Ici 1, failure t) ≤ delta := by
  exact actual_any_positive_round_failure_probability_is_at_most_the_budget
    P failure delta
    (actual_per_round_probability_assumptions_force_a_nonnegative_budget P failure delta hbound)
    hbound

end SafeLearning.CompleteModulesGPConfidenceBudgetConsequences
