import SafeLearning.CompletePolicyPenaltyConsequences
import SafeLearning.CompletePolicyBarrierRates

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompletePolicyPenaltyRates

open SafeLearning.CompleteFoundationsPenaltyModels SafeLearning.CompletePolicyBarrierCentralPath
  SafeLearning.CompletePolicyPenaltyConsequences

theorem actual_objective_strictly_convex : StrictConvexOn ℝ univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  change (a * x + b * y - 2) ^ 2 < a * (x - 2) ^ 2 + b * (y - 2) ^ 2
  have hp := mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
  have he : a * (x - 2) ^ 2 + b * (y - 2) ^ 2 - (a * x + b * y - 2) ^ 2 =
      a * b * (x - y) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    ring
  linarith

theorem actual_quadratic_violation_tends_to_zero :
    Tendsto (fun μ : ℝ => candidate μ - 1) atTop (𝓝 0) := by
  have hden : Tendsto (fun μ : ℝ => 2 + μ) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_id
  have h : Tendsto (fun μ : ℝ => 2 / (2 + μ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have he : (fun μ : ℝ => candidate μ - 1) =ᶠ[atTop] (fun μ => 2 / (2 + μ)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with μ hμ
    exact (actual_penalty_candidate_violation μ hμ).1
  exact h.congr' he.symm

theorem actual_quadratic_candidate_tends_to_hard_optimum :
    Tendsto candidate atTop (𝓝 1) := by
  have h := actual_quadratic_violation_tends_to_zero.add_const 1
  simpa using h

theorem actual_quadratic_violation_relative_rate :
    Tendsto (fun μ : ℝ => μ * (candidate μ - 1)) atTop (𝓝 2) := by
  have h : Tendsto (fun μ : ℝ => 2 - 2 * (candidate μ - 1)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul actual_quadratic_violation_tends_to_zero) :
      Tendsto (fun μ : ℝ => 2 - 2 * (candidate μ - 1)) atTop (𝓝 (2 - 2 * 0)))
  have he : (fun μ : ℝ => μ * (candidate μ - 1)) =ᶠ[atTop]
      (fun μ => 2 - 2 * (candidate μ - 1)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with μ hμ
    rw [(actual_penalty_candidate_violation μ hμ).1]
    have hd : 2 + μ ≠ 0 := by linarith
    field_simp
    <;> ring
  exact h.congr' he.symm

theorem actual_literal_barrier_multiplier (t : ℝ) :
    -1 / (t * constraint (centralPoint t)) = centralMultiplier t := by
  dsimp [constraint, centralPoint, centralMultiplier]
  ring

theorem actual_finite_barrier_multiplier_above_kkt (t : ℝ) (ht : 0 < t) :
    2 < centralMultiplier t := by
  rw [actual_central_multiplier_identity t ht]
  linarith [actual_central_slack_positive t ht]

theorem actual_linear_below_threshold_has_no_global_minimum (κ : ℝ) (hκ : κ < 1) :
    ¬ ∃ x : ℝ, ∀ y : ℝ, linearPenalty κ x ≤ linearPenalty κ y := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := actual_linear_below_threshold_unbounded κ (linearPenalty κ x) hκ
  exact (not_lt_of_ge (hx y)) hy

end SafeLearning.CompletePolicyPenaltyRates
