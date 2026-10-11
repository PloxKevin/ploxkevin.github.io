import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPNumerics

theorem exp_fourth_power_identity (value : ℝ) :
    Real.exp value=(Real.exp (value/4))^4 := by
  convert Real.exp_nat_mul (value/4) 4 using 1 <;> ring

theorem log_twenty_enclosure :
    (299573227/100000000:ℝ)<Real.log 20 ∧ Real.log 20<(299573228/100000000:ℝ) := by
  have hlo := Real.exp_bound (x:=(299573227/400000000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  have hhi := Real.exp_bound (x:=(299573228/400000000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hlo hhi
  have helo : Real.exp (299573227/400000000:ℝ)≤2114742526/1000000000 := by
    have h := (abs_le.mp hlo).2
    linarith
  have hehi : (2114742529/1000000000:ℝ)≤Real.exp (299573228/400000000:ℝ) := by
    have h := (abs_le.mp hhi).1
    linarith
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<20)).mpr
    rw [exp_fourth_power_identity]
    have hp : (Real.exp (299573227/400000000:ℝ))^4≤(2114742526/1000000000:ℝ)^4 := by
      gcongr
    have hrat : (2114742526/1000000000:ℝ)^4<20 := by norm_num
    convert hp.trans_lt hrat using 1 <;> norm_num
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<20)).mpr
    rw [exp_fourth_power_identity]
    have hp : (2114742529/1000000000:ℝ)^4≤(Real.exp (299573228/400000000:ℝ))^4 := by
      gcongr
    have hrat : (20:ℝ)<(2114742529/1000000000:ℝ)^4 := by norm_num
    convert hrat.trans_le hp using 1 <;> norm_num

theorem log_fifteen_fourths_enclosure :
    (13217558/10000000:ℝ)<Real.log (15/4) ∧
      Real.log (15/4)<(13217559/10000000:ℝ) := by
  have hlo := Real.exp_bound (x:=(13217558/40000000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  have hhi := Real.exp_bound (x:=(13217559/40000000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hlo hhi
  have helo : Real.exp (13217558/40000000:ℝ)≤1391578828/1000000000 := by
    have h := (abs_le.mp hlo).2
    linarith
  have hehi : (1391578862/1000000000:ℝ)≤Real.exp (13217559/40000000:ℝ) := by
    have h := (abs_le.mp hhi).1
    linarith
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<15/4)).mpr
    rw [exp_fourth_power_identity]
    have hp : (Real.exp (13217558/40000000:ℝ))^4≤(1391578828/1000000000:ℝ)^4 := by gcongr
    have hrat : (1391578828/1000000000:ℝ)^4<15/4 := by norm_num
    convert hp.trans_lt hrat using 1 <;> norm_num
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<15/4)).mpr
    rw [exp_fourth_power_identity]
    have hp : (1391578862/1000000000:ℝ)^4≤(Real.exp (13217559/40000000:ℝ))^4 := by gcongr
    have hrat : (15/4:ℝ)<(1391578862/1000000000:ℝ)^4 := by norm_num
    convert hrat.trans_le hp using 1 <;> norm_num

theorem information_gain_printed_rounding :
    |(1/2)*Real.log (15/4)-(660878/1000000:ℝ)|≤1/2000000 := by
  obtain ⟨hl,hu⟩ := log_fifteen_fourths_enclosure
  rw [abs_le]
  constructor <;> linarith

def confidenceMultiplier : ℝ := 2+(1/2)*Real.sqrt (3+2*Real.log 20)
def confidenceHalfWidth : ℝ := (1/5)*confidenceMultiplier

theorem confidence_multiplier_decimal_enclosure :
    (349928854/100000000:ℝ)≤confidenceMultiplier ∧
      confidenceMultiplier≤(349928855/100000000:ℝ) := by
  obtain ⟨hl,hu⟩ := log_twenty_enclosure
  have hp : 0≤3+2*Real.log 20 := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (3+2*Real.log 20)
  unfold confidenceMultiplier
  constructor <;> nlinarith

theorem confidence_multiplier_printed_rounding :
    |confidenceMultiplier-(34992885/10000000:ℝ)|≤1/20000000 := by
  obtain ⟨hl,hu⟩ := confidence_multiplier_decimal_enclosure
  rw [abs_le]
  constructor <;> linarith

theorem confidence_half_width_decimal_enclosure :
    (699857708/1000000000:ℝ)≤confidenceHalfWidth ∧
      confidenceHalfWidth≤(699857710/1000000000:ℝ) := by
  obtain ⟨hl,hu⟩ := confidence_multiplier_decimal_enclosure
  unfold confidenceHalfWidth
  constructor <;> linarith

theorem confidence_half_width_printed_rounding :
    |confidenceHalfWidth-(6998577/10000000:ℝ)|≤1/20000000 := by
  obtain ⟨hl,hu⟩ := confidence_half_width_decimal_enclosure
  rw [abs_le]
  constructor <;> linarith

theorem standard_deviation_of_nine_hundredths : Real.sqrt (9/100)=3/10 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
  norm_num

theorem general_inner_product_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (first second : H) : |inner ℝ first second|≤‖first‖*‖second‖ :=
  abs_real_inner_le_norm first second

end SafeLearning.CompleteModulesGPNumerics
