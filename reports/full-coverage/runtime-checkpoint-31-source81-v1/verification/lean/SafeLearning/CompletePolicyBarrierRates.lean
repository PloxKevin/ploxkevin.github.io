import SafeLearning.CompletePolicyBarrierCentralPath

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace SafeLearning.CompletePolicyBarrierRates

open SafeLearning.CompletePolicyBarrierCentralPath SafeLearning.CompleteFoundationsPenaltyModels

theorem actual_central_slack_relative_rate_identity (t : ℝ) (ht : 0 < t) :
    2 * t * centralSlack t = 1 / (1 + centralSlack t) := by
  have hu := actual_central_slack_positive t ht
  have he := (eq_div_iff (ne_of_gt ht)).mp (actual_central_slack_equation t ht)
  apply (eq_div_iff (show 1 + centralSlack t ≠ 0 by linarith)).2
  nlinarith

theorem actual_central_slack_asymptotic_relative_rate :
    Tendsto (fun t : ℝ => 2 * t * centralSlack t) atTop (𝓝 1) := by
  have hden : Tendsto (fun t : ℝ => 1 + centralSlack t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add actual_central_slack_tends_to_zero :
      Tendsto (fun t : ℝ => 1 + centralSlack t) atTop (𝓝 (1 + 0)))
  have h : Tendsto (fun t : ℝ => 1 / (1 + centralSlack t)) atTop (𝓝 1) := by
    simpa only [one_div, inv_one] using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have he : (fun t : ℝ => 2 * t * centralSlack t) =ᶠ[atTop]
      (fun t : ℝ => 1 / (1 + centralSlack t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact actual_central_slack_relative_rate_identity t ht
  exact h.congr' he.symm

theorem actual_central_multiplier_square_root_formula (t : ℝ) (ht : 0 < t) :
    centralMultiplier t = 1 + Real.sqrt (1 + 2 / t) := by
  rw [actual_central_multiplier_identity t ht]
  dsimp [centralSlack]
  ring

theorem actual_central_multiplier_ten_decimal_enclosure :
    (2095 / 1000 : ℝ) < centralMultiplier 10 ∧ centralMultiplier 10 < 2096 / 1000 := by
  rw [actual_central_multiplier_square_root_formula 10 (by norm_num)]
  have hs := Real.sq_sqrt (show 0 ≤ (1 + 2 / 10 : ℝ) by norm_num)
  have hp := Real.sqrt_nonneg (1 + 2 / 10 : ℝ)
  norm_num at hs hp ⊢
  constructor <;> nlinarith

theorem actual_central_multiplier_hundred_decimal_enclosure :
    (2009 / 1000 : ℝ) < centralMultiplier 100 ∧ centralMultiplier 100 < 2010 / 1000 := by
  rw [actual_central_multiplier_square_root_formula 100 (by norm_num)]
  have hs := Real.sq_sqrt (show 0 ≤ (1 + 2 / 100 : ℝ) by norm_num)
  have hp := Real.sqrt_nonneg (1 + 2 / 100 : ℝ)
  norm_num at hs hp ⊢
  constructor <;> nlinarith

theorem actual_central_ten_objective_gap_decimal_enclosure :
    (975 / 10000 : ℝ) < objective (centralPoint 10) - objective 1 ∧
      objective (centralPoint 10) - objective 1 < 985 / 10000 := by
  have hu := actual_central_slack_positive 10 (by norm_num)
  have he := actual_central_slack_equation 10 (by norm_num)
  have hb := actual_central_slack_asymptotic_error_bound 10 (by norm_num)
  have hm := actual_central_multiplier_ten_decimal_enclosure
  rw [actual_central_multiplier_identity 10 (by norm_num)] at hm
  rw [(actual_central_objective_gap 10 (by norm_num)).1]
  norm_num at he hb hm ⊢
  constructor <;> nlinarith [mul_self_nonneg (centralSlack 10)]

theorem actual_source_rounded_multipliers_are_not_literal_equalities :
    centralMultiplier 10 ≠ (210 / 100 : ℝ) ∧
      centralMultiplier 100 ≠ (201 / 100 : ℝ) := by
  have ht := actual_central_multiplier_ten_decimal_enclosure
  have hh := actual_central_multiplier_hundred_decimal_enclosure
  constructor <;> intro h <;> linarith

end SafeLearning.CompletePolicyBarrierRates
