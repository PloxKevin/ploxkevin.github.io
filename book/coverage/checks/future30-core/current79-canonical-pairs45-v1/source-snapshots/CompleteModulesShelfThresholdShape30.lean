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
  rw [←he]
  ring

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
    simpa only [abs_one, one_div] using
      (div_le_one ht).mpr (show (1:ℝ) ≤ tau by linarith)
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
    norm_num [abs_div, abs_of_pos ht] at h
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
      have h := abs_add_le (2*r1) (-r2)
      norm_num [abs_mul, abs_neg, ←sub_eq_add_neg] at h
      exact h
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
    _ ≤ 15/tau+7/tau := add_le_add hb le_rfl
    _ = 22/tau := by ring

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

namespace SafeLearning.CompleteModulesShelfThresholdShape30

theorem actual_exp_one_rational_enclosure :
    (2718281/1000000:ℝ) ≤ Real.exp (1) ∧
    Real.exp (1) ≤ (2718283/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(1:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_neg_one_rational_enclosure :
    (367879/1000000:ℝ) ≤ Real.exp (-1) ∧
    Real.exp (-1) ≤ (367880/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-1:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_half_rational_enclosure :
    (1648721/1000000:ℝ) ≤ Real.exp (1/2) ∧
    Real.exp (1/2) ≤ (1648722/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(1/2:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_fifth_rational_enclosure :
    (1221402/1000000:ℝ) ≤ Real.exp (1/5) ∧
    Real.exp (1/5) ≤ (1221403/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(1/5:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_neg_four_fifths_rational_enclosure :
    (449328/1000000:ℝ) ≤ Real.exp (-4/5) ∧
    Real.exp (-4/5) ≤ (449330/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-4/5:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_twentieth_rational_enclosure :
    (1051271/1000000:ℝ) ≤ Real.exp (1/20) ∧
    Real.exp (1/20) ≤ (1051272/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(1/20:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_neg_fifth_rational_enclosure :
    (818730/1000000:ℝ) ≤ Real.exp (-1/5) ∧
    Real.exp (-1/5) ≤ (818731/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-1/5:ℝ)) (by norm_num) (n:=12) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exponential_natural_multiple_enclosure
    (x lo hi : ℝ) (n : ℕ) (hlo : 0 ≤ lo)
    (hb : lo ≤ Real.exp x ∧ Real.exp x ≤ hi) :
    lo^n ≤ Real.exp (n*x) ∧ Real.exp (n*x) ≤ hi^n := by
  rw [Real.exp_nat_mul]
  constructor
  · gcongr
    exact hb.1
  · gcongr
    exact hb.2

theorem actual_shelf_tau1_failure1_two_decimal_rounding :
    (883/200:ℝ) < shelfThreshold 5 (1) (1) ∧
    shelfThreshold 5 (1) (1) < (885/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1) (2718281/1000000) (2718283/1000000) 1
    (by norm_num) actual_exp_one_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-1) (367879/1000000) (367880/1000000) 4
    (by norm_num) actual_exp_neg_one_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

theorem actual_shelf_tau1_failure2_two_decimal_rounding :
    (2745/200:ℝ) < shelfThreshold 5 (2) (1) ∧
    shelfThreshold 5 (2) (1) < (2747/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1) (2718281/1000000) (2718283/1000000) 2
    (by norm_num) actual_exp_one_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-1) (367879/1000000) (367880/1000000) 3
    (by norm_num) actual_exp_neg_one_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

theorem actual_shelf_tau_half_two_decimal_rounding :
    (1377/200:ℝ) < shelfThreshold 5 (1) (1/2) ∧
    shelfThreshold 5 (1) (1/2) < (1379/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1) (2718281/1000000) (2718283/1000000) 2
    (by norm_num) actual_exp_one_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-1) (367879/1000000) (367880/1000000) 8
    (by norm_num) actual_exp_neg_one_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

theorem actual_shelf_tau_two_two_decimal_rounding :
    (863/200:ℝ) < shelfThreshold 5 (1) (2) ∧
    shelfThreshold 5 (1) (2) < (865/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1/2) (1648721/1000000) (1648722/1000000) 1
    (by norm_num) actual_exp_half_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-1) (367879/1000000) (367880/1000000) 2
    (by norm_num) actual_exp_neg_one_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

theorem actual_shelf_tau_five_two_decimal_rounding :
    (993/200:ℝ) < shelfThreshold 5 (1) (5) ∧
    shelfThreshold 5 (1) (5) < (995/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1/5) (1221402/1000000) (1221403/1000000) 1
    (by norm_num) actual_exp_fifth_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-4/5) (449328/1000000) (449330/1000000) 1
    (by norm_num) actual_exp_neg_four_fifths_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

theorem actual_shelf_tau_twenty_two_decimal_rounding :
    (1135/200:ℝ) < shelfThreshold 5 (1) (20) ∧
    shelfThreshold 5 (1) (20) < (1137/200:ℝ) := by
  have ep := actual_exponential_natural_multiple_enclosure (1/20) (1051271/1000000) (1051272/1000000) 1
    (by norm_num) actual_exp_twentieth_rational_enclosure
  norm_num at ep
  have en := actual_exponential_natural_multiple_enclosure (-1/5) (818730/1000000) (818731/1000000) 1
    (by norm_num) actual_exp_neg_fifth_rational_enclosure
  norm_num at en
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  constructor <;> linarith [ep.1,ep.2,en.1,en.2]

/-- A parameter-uniform explicit second-order expansion of the actual shelf expression. -/
theorem actual_shelf_generic_second_order_remainder
    (a b tau : ℝ) (ht : 0 < tau) (hb : |b| ≤ tau) (hba : |b-a| ≤ tau) :
    |shelfThreshold a b tau -
      (a+b+(a*b+b^2/2-a^2/2)/tau)| ≤
      ((2/9:ℝ)*(2*|b|^3+|b-a|^3))/tau^2 := by
  have htne := ne_of_gt ht
  have hx1 : |b/tau| ≤ 1 := by
    rw [abs_div,abs_of_pos ht]
    exact (div_le_one ht).mpr hb
  have hx2 : |(b-a)/tau| ≤ 1 := by
    rw [abs_div,abs_of_pos ht]
    exact (div_le_one ht).mpr hba
  let r1 := Real.exp (b/tau) - (1+b/tau+(b/tau)^2/2)
  let r2 := Real.exp ((b-a)/tau) - (1+(b-a)/tau+((b-a)/tau)^2/2)
  have h1 : |r1| ≤ (2/9:ℝ)*(|b|/tau)^3 := by
    simpa only [r1,abs_div,abs_of_pos ht] using actual_exp_quadratic_remainder_bound (b/tau) hx1
  have h2 : |r2| ≤ (2/9:ℝ)*(|b-a|/tau)^3 := by
    simpa only [r2,abs_div,abs_of_pos ht] using actual_exp_quadratic_remainder_bound ((b-a)/tau) hx2
  have hid : shelfThreshold a b tau-(a+b+(a*b+b^2/2-a^2/2)/tau)=tau*(2*r1-r2) := by
    rw [actual_shelf_threshold_equivalent_form]
    dsimp [r1,r2]
    field_simp
    ring
  rw [hid,abs_mul,abs_of_pos ht]
  calc
    tau*|2*r1-r2| ≤ tau*(2*|r1|+|r2|) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      have h := abs_add_le (2*r1) (-r2)
      norm_num [abs_mul,abs_neg,←sub_eq_add_neg] at h
      exact h
    _ ≤ tau*((4/9:ℝ)*(|b|/tau)^3+(2/9:ℝ)*(|b-a|/tau)^3) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      nlinarith [h1,h2]
    _ = ((2/9:ℝ)*(2*|b|^3+|b-a|^3))/tau^2 := by field_simp; ring

end SafeLearning.CompleteModulesShelfThresholdShape30

namespace SafeLearning.CompleteModulesShelfThresholdShape30

theorem actual_shelf_p_itself_delay_ratio_rounds_to_three_point_one :
    (61/20:ℝ)<shelfThreshold 5 2 1/shelfThreshold 5 1 1 ∧
    shelfThreshold 5 2 1/shelfThreshold 5 1 1<(63/20:ℝ) := by
  have h1 := actual_shelf_tau1_failure1_two_decimal_rounding
  have h2 := actual_shelf_tau1_failure2_two_decimal_rounding
  have hp : 0<shelfThreshold 5 1 1 := by linarith [h1.1]
  constructor
  · exact (lt_div_iff₀ hp).mpr (by linarith [h1.2,h2.1])
  · exact (div_lt_iff₀ hp).mpr (by linarith [h1.1,h2.2])

theorem actual_shelf_exp_neg_five_four_decimal_rounding :
    (133/20000:ℝ)<Real.exp (-5) ∧ Real.exp (-5)<(135/20000:ℝ) := by
  have h := actual_exponential_natural_multiple_enclosure (-1) (367879/1000000) (367880/1000000) 5
    (by norm_num) actual_exp_neg_one_rational_enclosure
  norm_num at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_neg_half_rational_enclosure :
    (606528/1000000:ℝ)≤Real.exp (-1/2) ∧ Real.exp (-1/2)≤(606532/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-1/2:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_shelf_exp_neg_two_point_five_three_decimal_rounding :
    (163/2000:ℝ)<Real.exp (-5/2) ∧ Real.exp (-5/2)<(165/2000:ℝ) := by
  have h := actual_exponential_natural_multiple_enclosure (-1/2) (606528/1000000) (606532/1000000) 5
    (by norm_num) actual_exp_neg_half_rational_enclosure
  norm_num at h
  constructor <;> linarith [h.1,h.2]

theorem actual_shelf_exp_neg_one_three_decimal_rounding :
    (735/2000:ℝ)<Real.exp (-1) ∧ Real.exp (-1)<(737/2000:ℝ) := by
  have h := actual_exp_neg_one_rational_enclosure
  constructor <;> linarith [h.1,h.2]

theorem actual_shelf_exp_neg_quarter_three_decimal_rounding :
    (1557/2000:ℝ)<Real.exp (-1/4) ∧ Real.exp (-1/4)<(1559/2000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-1/4:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

end SafeLearning.CompleteModulesShelfThresholdShape30
