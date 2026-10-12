import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteModulesShelfThresholdShape30

/-- The actual displayed shelf threshold with travel-time a and failure bound b. -/
def shelfThreshold (a b tau : ℝ) : ℝ :=
  tau * (2 - Real.exp (-a/tau)) * Real.exp (b/tau) - tau

/-- Multiplication of the actual exponentials gives the equivalent single-exponential form. -/
theorem actual_shelf_threshold_equivalent_form (a b tau : ℝ) :
    shelfThreshold a b tau =
      tau * (2*Real.exp (b/tau) - Real.exp ((b-a)/tau) - 1) := by
  have he : Real.exp (-a/tau) * Real.exp (b/tau) = Real.exp ((b-a)/tau) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold shelfThreshold
  nlinarith [he]

/-- It is threshold plus tau that scales exactly with extra failure delay. -/
theorem actual_extra_failure_time_scales_the_shifted_threshold (a b tau delay : ℝ) :
    shelfThreshold a (b+delay) tau + tau =
      (shelfThreshold a b tau + tau) * Real.exp (delay/tau) := by
  unfold shelfThreshold
  rw [add_div, Real.exp_add]
  ring

/-- A genuine cubic Taylor bound for the real exponential on [-1,1]. -/
theorem actual_exp_quadratic_remainder_bound (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - (1+x+x^2/2)| ≤ (2/9:ℝ)*|x|^3 := by
  have h := Real.exp_bound hx (n:=3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  convert h using 1 <;> ring

/-- The printed a=5,b=1 asymptotic has a concrete rigorous remainder constant. -/
theorem actual_default_shelf_second_order_remainder (tau : ℝ) (htau : 4 ≤ tau) :
    |shelfThreshold 5 1 tau - (6-7/tau)| ≤ (44/3:ℝ)/tau^2 := by
  have ht : 0 < tau := by linarith
  have htne := ne_of_gt ht
  have hx1 : |(1:ℝ)/tau| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    norm_num
    exact (div_le_one ht).mpr (by linarith)
  have hx2 : |(-4:ℝ)/tau| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    norm_num
    exact (div_le_one ht).mpr htau
  let r1 := Real.exp (1/tau) - (1+1/tau+(1/tau)^2/2)
  let r2 := Real.exp (-4/tau) - (1-4/tau+(-4/tau)^2/2)
  have h1 : |r1| ≤ (2/9:ℝ)*(1/tau)^3 := by
    have h := actual_exp_quadratic_remainder_bound (1/tau) hx1
    simpa only [r1, abs_div, abs_one, abs_of_pos ht] using h
  have h2 : |r2| ≤ (2/9:ℝ)*(4/tau)^3 := by
    have h := actual_exp_quadratic_remainder_bound (-4/tau) hx2
    norm_num only [abs_div, abs_neg, abs_ofNat, abs_of_pos ht] at h
    simpa only [r2, sub_eq_add_neg, neg_div] using h
  have hid : shelfThreshold 5 1 tau - (6-7/tau) = tau*(2*r1-r2) := by
    rw [actual_shelf_threshold_equivalent_form]
    dsimp [r1,r2]
    norm_num
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos ht]
  calc
    tau*|2*r1-r2| ≤ tau*(2*|r1|+|r2|) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      simpa only [abs_mul, abs_ofNat] using abs_sub_le (2*r1) r2
    _ ≤ tau*((4/9:ℝ)*(1/tau)^3+(2/9:ℝ)*(4/tau)^3) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      nlinarith [h1,h2]
    _ = (44/3:ℝ)/tau^2 := by field_simp; ring

/-- The eventual approach is rigorously from below, not a extrapolation of samples. -/
theorem actual_default_shelf_is_below_six_for_every_tau_at_least_four
    (tau : ℝ) (htau : 4 ≤ tau) : shelfThreshold 5 1 tau < 6 := by
  have ht : 0 < tau := by linarith
  have h := (abs_le.mp (actual_default_shelf_second_order_remainder tau htau)).2
  have hk : (44/3:ℝ)/tau^2 < 7/tau := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos ht) ht).mpr
    have hh := mul_lt_mul_of_pos_left (show (44/3:ℝ) < 7*tau by linarith) ht
    nlinarith [hh]
  linarith

/-- The displayed 5.93 at tau100 has a genuine two-decimal rounding enclosure. -/
theorem actual_default_shelf_tau100_rounds_to_five_point_ninety_three :
    (1185/200:ℝ) < shelfThreshold 5 1 100 ∧
    shelfThreshold 5 1 100 < (1187/200:ℝ) := by
  have h := abs_le.mp (actual_default_shelf_second_order_remainder 100 (by norm_num))
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- A uniform first-order bound makes the limiting cancellation explicit. -/
theorem actual_default_shelf_absolute_limit_error (tau : ℝ) (htau : 4 ≤ tau) :
    |shelfThreshold 5 1 tau - 6| ≤ 22/tau := by
  have ht : 0 < tau := by linarith
  have hr := actual_default_shelf_second_order_remainder tau htau
  have hb : (44/3:ℝ)/tau^2 ≤ 15/tau := by
    apply (div_le_div_iff₀ (sq_pos_of_pos ht) ht).mpr
    have hh := mul_le_mul_of_nonneg_left (show (44/3:ℝ) ≤ 15*tau by linarith) ht.le
    nlinarith [hh]
  calc
    |shelfThreshold 5 1 tau-6| =
      |(shelfThreshold 5 1 tau-(6-7/tau))+((6-7/tau)-6)| := by congr 1; ring
    _ ≤ |shelfThreshold 5 1 tau-(6-7/tau)| + |(6-7/tau)-6| := abs_add_le _ _
    _ ≤ (44/3:ℝ)/tau^2+7/tau := by
      apply add_le_add hr
      rw [show (6-7/tau)-6 = -(7/tau) by ring, abs_neg, abs_of_pos (div_pos (by norm_num) ht)]
    _ ≤ 22/tau := by linarith [hb]

/-- The actual expression tends to the displayed finite limit six. -/
theorem actual_default_shelf_tends_to_six :
    Tendsto (fun tau : ℝ => shelfThreshold 5 1 tau) atTop (𝓝 6) := by
  refine Metric.tendsto_atTop.mpr (fun eps heps => ?_)
  refine ⟨max 4 (22/eps+1), fun tau htau => ?_⟩
  have h4 : 4 ≤ tau := le_trans (le_max_left _ _) htau
  have ht : 0 < tau := by linarith
  have he : 22/eps < tau := by linarith [le_trans (le_max_right _ _) htau]
  have hsmall : 22/tau < eps := (div_lt_iff₀ ht).mpr (by
    have h := (div_lt_iff₀ heps).mp he
    nlinarith [h])
  simpa only [Real.dist_eq] using (actual_default_shelf_absolute_limit_error tau h4).trans_lt hsmall

end SafeLearning.CompleteModulesShelfThresholdShape30
