import SafeLearning.CompleteAppliedGridConfidence
import SafeLearning.CoreAnalysis
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedValidationNumbers
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem log20_enclosure : (2995732/1000000:ℝ)<Real.log 20 ∧
    Real.log 20<(5991465/2000000:ℝ) := by
  have heq : Real.log (400:ℝ)=2*Real.log 20 := by
    rw [show (400:ℝ)=20^2 by norm_num,Real.log_pow]
    norm_num
  obtain ⟨hl,hu⟩ := SafeLearning.CompleteAppliedGridConfidence.log400_enclosure
  constructor <;> linarith

/-- These rational bounds certify rounding to six places, without decimal floating point. -/
theorem validation_radius_rounding :
    (387015/10000000:ℝ)<Real.sqrt (Real.log 20/2000) ∧
    Real.sqrt (Real.log 20/2000)<387025/10000000 := by
  obtain ⟨hl,hu⟩ := log20_enclosure
  have hs := Real.sq_sqrt (show 0≤Real.log (20:ℝ)/2000 by positivity)
  have hn := Real.sqrt_nonneg (Real.log (20:ℝ)/2000)
  constructor <;> nlinarith

theorem validation_radius_rounded_038702 :
    |Real.sqrt (Real.log 20/2000)-(38702/1000000:ℝ)|<1/2000000 := by
  obtain ⟨hl,hu⟩ := validation_radius_rounding
  rw [abs_lt]
  constructor <;> linarith

theorem validation_radius_exceeds_one_percent :
    (1/100:ℝ)<Real.sqrt (Real.log 20/2000) :=
  SafeLearning.CoreAnalysis.hoeffding_radius_above_target

/-- A direct exponential-series remainder certifies the small logarithm used in zero-failure tests. -/
theorem log99_enclosure :
    -(100503359/10000000000:ℝ)<Real.log (99/100:ℝ) ∧
    Real.log (99/100:ℝ) < -(100503358/10000000000:ℝ) := by
  have hb₁ := Real.exp_bound (x := -(100503359/10000000000:ℝ)) (by norm_num)
    (n := 6) (by norm_num)
  have hb₂ := Real.exp_bound (x := -(100503358/10000000000:ℝ)) (by norm_num)
    (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb₁ hb₂
  have h₁ : Real.exp (-(100503359/10000000000:ℝ))<99/100 := by
    linarith [(abs_le.mp hb₁).2]
  have h₂ : (99/100:ℝ)<Real.exp (-(100503358/10000000000:ℝ)) := by
    linarith [(abs_le.mp hb₂).1]
  rw [← Real.exp_log (by norm_num : (0:ℝ)<99/100)] at h₁ h₂
  exact ⟨Real.exp_lt_exp.mp h₁,Real.exp_lt_exp.mp h₂⟩

theorem single_log_ratio_rounding :
    |Real.log (1/20:ℝ)/Real.log (99/100:ℝ)-(298073/1000:ℝ)|<1/2000 := by
  obtain ⟨hl,hu⟩ := log20_enclosure
  obtain ⟨hd₁,hd₂⟩ := log99_enclosure
  have hd : Real.log (99/100:ℝ)<0 := by linarith
  have hn : Real.log (1/20:ℝ)=-Real.log 20 := by
    rw [show (1/20:ℝ)=(20:ℝ)⁻¹ by norm_num,Real.log_inv]
  have hlo : (2980725/10000:ℝ)<Real.log (1/20:ℝ)/Real.log (99/100:ℝ) := by
    rw [hn,lt_div_iff_of_neg hd]
    nlinarith
  have hhi : Real.log (1/20:ℝ)/Real.log (99/100:ℝ)<2980735/10000 := by
    rw [hn,div_lt_iff_of_neg hd]
    nlinarith
  rw [abs_lt]
  constructor <;> linarith

theorem twenty_log_ratio_rounding :
    |Real.log (1/400:ℝ)/Real.log (99/100:ℝ)-(596146/1000:ℝ)|<1/2000 := by
  obtain ⟨hl,hu⟩ := SafeLearning.CompleteAppliedGridConfidence.log400_enclosure
  obtain ⟨hd₁,hd₂⟩ := log99_enclosure
  have hd : Real.log (99/100:ℝ)<0 := by linarith
  have hn : Real.log (1/400:ℝ)=-Real.log 400 := by
    rw [show (1/400:ℝ)=(400:ℝ)⁻¹ by norm_num,Real.log_inv]
  have hlo : (5961455/10000:ℝ)<Real.log (1/400:ℝ)/Real.log (99/100:ℝ) := by
    rw [hn,lt_div_iff_of_neg hd]
    nlinarith
  have hhi : Real.log (1/400:ℝ)/Real.log (99/100:ℝ)<5961465/10000 := by
    rw [hn,div_lt_iff_of_neg hd]
    nlinarith
  rw [abs_lt]
  constructor <;> linarith

theorem single_real_sample_minimum (n : ℕ) :
    (99/100:ℝ)^n≤1/20 ↔ 299≤n := by
  have h := SafeLearning.CoreAnalysis.validation_single_minimal n
  have heq : ((99/100:ℚ)^n≤1/20) ↔ ((99/100:ℝ)^n≤1/20) := by
    have hc := (Rat.cast_le (K := ℝ) (p := (99/100:ℚ)^n) (q := (1/20:ℚ))).symm
    push_cast at hc
    exact hc
  exact heq.symm.trans h

theorem twenty_real_sample_minimum (n : ℕ) :
    (99/100:ℝ)^n≤1/400 ↔ 597≤n := by
  have h := SafeLearning.CoreAnalysis.validation_twenty_minimal n
  have heq : ((99/100:ℚ)^n≤1/400) ↔ ((99/100:ℝ)^n≤1/400) := by
    have hc := (Rat.cast_le (K := ℝ) (p := (99/100:ℚ)^n) (q := (1/400:ℚ))).symm
    push_cast at hc
    exact hc
  exact heq.symm.trans h

/-- The logarithmic rule follows from the actual positive base, not from its rounded decimal. -/
theorem exact_log_sample_threshold (n : ℕ) (delta : ℝ) (hd : 0<delta) :
    (99/100:ℝ)^n≤delta ↔ Real.log delta/Real.log (99/100:ℝ)≤n := by
  have hb : Real.log (99/100:ℝ)<0 := Real.log_neg (by norm_num) (by norm_num)
  have hpow : Real.exp ((n:ℝ)*Real.log (99/100:ℝ))=(99/100:ℝ)^n := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hl : (99/100:ℝ)^n≤delta ↔ (n:ℝ)*Real.log (99/100:ℝ)≤Real.log delta := by
    rw [← hpow]
    conv_lhs => rhs;rw [← Real.exp_log hd]
    exact Real.exp_le_exp
  rw [hl,div_le_iff_of_neg hb]

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem single_power_strict : (99/100:ℝ)^299<1/20 := by
  norm_num [div_pow]

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem twenty_power_strict : (99/100:ℝ)^597<1/400 := by
  norm_num [div_pow]

end SafeLearning.CompleteAppliedValidationNumbers
