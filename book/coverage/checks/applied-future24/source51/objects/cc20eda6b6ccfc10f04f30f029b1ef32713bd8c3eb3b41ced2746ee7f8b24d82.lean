import SafeLearning.CompleteFoundationsExactPenaltyModels

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompletePolicyBarrierCentralPath

open SafeLearning.CompleteFoundationsPenaltyModels

def centralSlack (t : ℝ) : ℝ := (Real.sqrt (1 + 2 / t) - 1) / 2
def centralPoint (t : ℝ) : ℝ := 1 - centralSlack t
def centralMultiplier (t : ℝ) : ℝ := 1 / (t * centralSlack t)
def barrierObjective (t x : ℝ) : ℝ := objective x - Real.log (1 - x) / t

theorem actual_central_slack_positive (t : ℝ) (ht : 0 < t) : 0 < centralSlack t := by
  have hp : 0 < 2 / t := div_pos (by norm_num) ht
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 2 / t by linarith)
  have hn := Real.sqrt_nonneg (1 + 2 / t)
  unfold centralSlack
  nlinarith

theorem actual_central_slack_equation (t : ℝ) (ht : 0 < t) :
    2 * (centralSlack t) ^ 2 + 2 * centralSlack t = 1 / t := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 2 / t by positivity)
  have hr : (Real.sqrt (1 + 2 / t)) ^ 2 = 1 + 2 * (1 / t) := hs.trans (by ring)
  dsimp [centralSlack]
  nlinarith only [hr]

theorem actual_central_point_strictly_feasible (t : ℝ) (ht : 0 < t) :
    centralPoint t < 1 ∧ constraint (centralPoint t) < 0 := by
  have h := actual_central_slack_positive t ht
  dsimp [centralPoint, constraint]
  constructor <;> linarith

theorem actual_central_multiplier_identity (t : ℝ) (ht : 0 < t) :
    centralMultiplier t = 2 + 2 * centralSlack t := by
  have hu := actual_central_slack_positive t ht
  have he : (2 + 2 * centralSlack t) * centralSlack t = 1 / t := by
    nlinarith [actual_central_slack_equation t ht]
  have hm := (eq_div_iff (ne_of_gt ht)).mp he
  unfold centralMultiplier
  apply (div_eq_iff (ne_of_gt (mul_pos ht hu))).2
  nlinarith

theorem actual_barrier_derivative (t x : ℝ) (hx : x < 1) :
    HasDerivAt (barrierObjective t) (2 * (x - 2) + 1 / (t * (1 - x))) x := by
  have hlog := (Real.hasDerivAt_log (show 1 - x ≠ 0 by linarith)).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  convert (actual_objective_derivative x).sub (hlog.div_const t) using 1
  · rfl
  · simp only [zero_sub, mul_neg, mul_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem actual_central_point_stationary (t : ℝ) (ht : 0 < t) :
    HasDerivAt (barrierObjective t) 0 (centralPoint t) := by
  have hd := actual_barrier_derivative t (centralPoint t)
    (actual_central_point_strictly_feasible t ht).1
  convert hd using 1
  have hm := actual_central_multiplier_identity t ht
  dsimp [centralPoint, centralMultiplier] at hm ⊢
  have he : 1 - (1 - centralSlack t) = centralSlack t := by ring
  rw [he]
  linarith

theorem actual_central_point_global_quadratic_gap (t x : ℝ) (ht : 0 < t) (hx : x < 1) :
    barrierObjective t (centralPoint t) + (x - centralPoint t) ^ 2 ≤
      barrierObjective t x := by
  have hu := actual_central_slack_positive t ht
  have hv : 0 < 1 - x := sub_pos.mpr hx
  have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at hlog
  have hd := div_le_div_of_nonneg_right hlog ht.le
  have ha : ((1 - x) / centralSlack t - 1) / t =
      -centralMultiplier t * (x - centralPoint t) := by
    dsimp [centralMultiplier, centralPoint]
    field_simp
    <;> ring
  have hb : objective x - objective (centralPoint t) =
      (x - centralPoint t) ^ 2 - centralMultiplier t * (x - centralPoint t) := by
    rw [actual_central_multiplier_identity t ht]
    dsimp [objective, centralPoint]
    ring
  rw [ha, sub_div] at hd
  dsimp [barrierObjective]
  have hc : 1 - centralPoint t = centralSlack t := by dsimp [centralPoint];ring
  rw [hc]
  linarith

theorem actual_central_point_unique_global_minimum (t x : ℝ) (ht : 0 < t) (hx : x < 1) :
    barrierObjective t (centralPoint t) ≤ barrierObjective t x ∧
    (barrierObjective t x = barrierObjective t (centralPoint t) ↔ x = centralPoint t) := by
  have h := actual_central_point_global_quadratic_gap t x ht hx
  refine ⟨by nlinarith [sq_nonneg (x - centralPoint t)], ?_⟩
  constructor
  · intro he
    have hz : (x - centralPoint t) ^ 2 = 0 := by nlinarith [sq_nonneg (x - centralPoint t)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    rfl

theorem actual_central_objective_gap (t : ℝ) (ht : 0 < t) :
    objective (centralPoint t) - objective 1 =
      1 / t - (centralSlack t) ^ 2 ∧
    0 < objective (centralPoint t) - objective 1 ∧
    objective (centralPoint t) - objective 1 ≤ 1 / t := by
  have he := actual_central_slack_equation t ht
  have hp := actual_central_slack_positive t ht
  dsimp [objective, centralPoint]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (centralSlack t)]

theorem actual_central_slack_asymptotic_error_bound (t : ℝ) (ht : 0 < t) :
    centralSlack t ≤ 1 / (2 * t) ∧
    |centralSlack t - 1 / (2 * t)| = (centralSlack t) ^ 2 := by
  have he := actual_central_slack_equation t ht
  have hi : 1 / (2 * t) = (1 / t) / 2 := by ring
  rw [hi]
  have h : centralSlack t - (1 / t) / 2 = -(centralSlack t) ^ 2 := by nlinarith
  refine ⟨by nlinarith [sq_nonneg (centralSlack t)], ?_⟩
  rw [h, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem actual_central_slack_tends_to_zero :
    Tendsto centralSlack atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ha : Tendsto (fun t : ℝ => 1 + 2 / t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add h :
      Tendsto (fun t : ℝ => 1 + 2 / t) atTop (𝓝 (1 + 0)))
  have hs := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp ha
  convert (hs.sub tendsto_const_nhds).div_const 2 using 1
  · rfl
  · norm_num

theorem actual_central_multiplier_tends_to_kkt_multiplier :
    Tendsto centralMultiplier atTop (𝓝 2) := by
  have h : Tendsto (fun t : ℝ => 2 + 2 * centralSlack t) atTop (𝓝 (2 + 2 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul actual_central_slack_tends_to_zero)
  have he : centralMultiplier =ᶠ[atTop] fun t : ℝ => 2 + 2 * centralSlack t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact actual_central_multiplier_identity t ht
  have hh : Tendsto (fun t : ℝ => 2 + 2 * centralSlack t) atTop (𝓝 2) := by
    simpa using h
  exact hh.congr' he.symm

end SafeLearning.CompletePolicyBarrierCentralPath
