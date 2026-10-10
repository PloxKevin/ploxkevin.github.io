import Mathlib

set_option autoImplicit false
noncomputable section
open Finset
namespace SafeLearning.CompletePolicyBenchmarkRatios

/-- The report's epsilon-protected normalized final violation. -/
def normalizedExcess (cost budget reference ε : ℝ) : ℝ :=
  max 0 (cost - budget) / max ε (reference - budget)

/-- The report's cost rate over the complete training run. -/
def trainingRate (totalCost steps : ℝ) : ℝ := totalCost / steps

theorem actual_normalizer_positive (reference budget ε : ℝ) (hε : 0 < ε) :
    0 < max ε (reference - budget) := lt_of_lt_of_le hε (le_max_left _ _)

theorem actual_normalized_excess_nonnegative (cost budget reference ε : ℝ) (hε : 0 < ε) :
    0 ≤ normalizedExcess cost budget reference ε :=
  div_nonneg (le_max_left _ _) (le_of_lt (actual_normalizer_positive reference budget ε hε))

theorem actual_zero_normalized_excess_iff_feasible (cost budget reference ε : ℝ)
    (hε : 0 < ε) : normalizedExcess cost budget reference ε = 0 ↔ cost ≤ budget := by
  have hd := ne_of_gt (actual_normalizer_positive reference budget ε hε)
  simp only [normalizedExcess, div_eq_zero_iff, hd, or_false]
  constructor
  · intro h
    have := le_max_right (0 : ℝ) (cost - budget)
    rw [h] at this
    linarith
  · intro h
    exact max_eq_left (by linarith)

theorem actual_positive_normalized_excess_iff_violation (cost budget reference ε : ℝ)
    (hε : 0 < ε) : 0 < normalizedExcess cost budget reference ε ↔ budget < cost := by
  have hn := actual_normalized_excess_nonnegative cost budget reference ε hε
  have hz := actual_zero_normalized_excess_iff_feasible cost budget reference ε hε
  constructor
  · intro hp
    by_contra h
    have he := hz.mpr (le_of_not_gt h)
    linarith
  · intro hv
    have he : normalizedExcess cost budget reference ε ≠ 0 := by
      intro h
      exact (not_le_of_gt hv) (hz.mp h)
    exact lt_of_le_of_ne hn (Ne.symm he)

theorem actual_rate_implies_episode_cost (rate reference ratio : ℝ)
    (h : rate / reference = ratio) (href : reference ≠ 0) : rate = ratio * reference := by
  exact (div_eq_iff href).mp h

theorem actual_hypothetical_sg18_rates_and_episode_budget :
    (0.245 : ℝ) * 0.10 = 0.0245 ∧ (0.265 : ℝ) * 0.10 = 0.0265 ∧
    (0.646 : ℝ) * 0.10 = 0.0646 ∧ (0.0245 : ℝ) * 1000 = 24.5 ∧
    (0.0265 : ℝ) * 1000 = 26.5 ∧ (0.0646 : ℝ) * 1000 = 64.6 ∧
    (0.0245 : ℝ) * 1000 ≤ 25 ∧ ¬ (0.0265 * 1000 ≤ (25 : ℝ)) ∧
    ¬ (0.0646 * 1000 ≤ (25 : ℝ)) := by norm_num

theorem actual_exact_break_even_references_and_roundings :
    (0.025 : ℝ) / 0.245 = 5 / 49 ∧ (0.025 : ℝ) / 0.646 = 25 / 646 ∧
    0.1015 < (5 : ℝ) / 49 ∧ (5 : ℝ) / 49 < 0.1025 ∧
    0.0385 < (25 : ℝ) / 646 ∧ (25 : ℝ) / 646 < 0.0395 ∧
    (0.025 : ℝ) / 0.245 ≠ 0.102 ∧ (0.025 : ℝ) / 0.646 ≠ 0.039 := by norm_num

theorem actual_budget_threshold_for_positive_ratio (ratio reference : ℝ) (hr : 0 < ratio) :
    ratio * reference * 1000 ≤ 25 ↔ reference ≤ 0.025 / ratio := by
  constructor
  · intro h
    apply (le_div_iff₀ hr).mpr
    nlinarith
  · intro h
    have := (le_div_iff₀ hr).mp h
    nlinarith

theorem actual_average_of_ratios_is_not_ratio_of_averages :
    (((1 : ℝ) / 1 + 1 / 2) / 2 = 3 / 4) ∧
    (((1 : ℝ) + 1) / 2 / ((1 + 2) / 2) = 2 / 3) ∧
    (((1 : ℝ) / 1 + 1 / 2) / 2 ≠ ((1 + 1) / 2) / ((1 + 2) / 2)) := by norm_num

theorem actual_aggregate_ratio_does_not_identify_each_task :
    (((1 : ℝ) + 1 / 2) / 2 = (1 / 2 + 1) / 2) ∧
    ((1 : ℝ) ≠ 1 / 2) := by norm_num

theorem actual_positive_mean_violation_requires_a_violating_run {ι : Type*}
    (runs : Finset ι) (cost reference : ι → ℝ) (budget ε : ℝ) (hε : 0 < ε)
    (hmean : 0 < (∑ i ∈ runs, normalizedExcess (cost i) budget (reference i) ε) /
      (runs.card : ℝ)) : ∃ i ∈ runs, budget < cost i := by
  by_contra h
  push Not at h
  have hz : ∑ i ∈ runs, normalizedExcess (cost i) budget (reference i) ε = 0 := by
    apply sum_eq_zero
    intro i hi
    exact (actual_zero_normalized_excess_iff_feasible (cost i) budget (reference i) ε hε).mpr (h i hi)
  rw [hz, zero_div] at hmean
  exact lt_irrefl _ hmean

theorem actual_final_safety_and_large_training_cost_are_compatible :
    normalizedExcess 0 25 100 (0.000001 : ℝ) = 0 ∧
    trainingRate (100 + 0) (1000 + 1000) = (0.05 : ℝ) ∧
    trainingRate (100 + 0) (1000 + 1000) * 1000 > 25 := by
  norm_num [normalizedExcess, trainingRate]

theorem actual_feasible_training_mean_does_not_make_every_episode_feasible :
    (((50 : ℝ) + 0) / 2 ≤ 25) ∧ ¬ ((50 : ℝ) ≤ 25) := by norm_num

/-- The report's Pareto comparison of two feasible runs of equal length. -/
def feasibleRunDominates (returnA rateA returnB rateB : ℝ) : Prop :=
  (returnB ≤ returnA ∧ rateA < rateB) ∨ (returnB < returnA ∧ rateA ≤ rateB)

theorem actual_sg18_return_cost_tradeoff_has_no_pareto_winner :
    ¬ feasibleRunDominates 0.331 0.265 0.24 0.245 ∧
    ¬ feasibleRunDominates 0.24 0.245 0.331 0.265 := by
  norm_num [feasibleRunDominates]

theorem actual_nonnegative_cost_shaping_is_an_upper_bound (cost bonus budget : ℝ)
    (hb : 0 ≤ bonus) (hshaped : cost + bonus ≤ budget) : cost ≤ budget := by linarith

theorem actual_optimistic_error_at_active_estimated_boundary_violates_budget
    (actualCost estimate budget error : ℝ) (hactive : estimate = budget)
    (herror : actualCost = estimate + error) (hp : 0 < error) : budget < actualCost := by linarith

end SafeLearning.CompletePolicyBenchmarkRatios
