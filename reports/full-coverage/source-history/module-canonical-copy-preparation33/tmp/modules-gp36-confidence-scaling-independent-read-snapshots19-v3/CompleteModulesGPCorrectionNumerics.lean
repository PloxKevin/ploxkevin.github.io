import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SafeLearning.CompleteModulesGPCorrectionNumerics
open CompleteModulesGPNumerics

def originalNoise : ℝ := (1/10)*Real.sqrt (Real.log 2-2*Real.log (1/20))
def correctedNoise : ℝ := Real.sqrt (Real.log 101-2*Real.log (1/20))

theorem actual_log_delta_is_the_negative_log_twenty :
    Real.log (1/20:ℝ)=-Real.log 20 := by
  rw [show (1/20:ℝ)=(20:ℝ)⁻¹ by norm_num,Real.log_inv]

theorem actual_minus_twice_log_delta_decimal_enclosure :
    (599146454/100000000:ℝ)< -2*Real.log (1/20) ∧
      -2*Real.log (1/20)<(599146456/100000000:ℝ) := by
  rw [actual_log_delta_is_the_negative_log_twenty]
  obtain ⟨hl,hu⟩ := log_twenty_enclosure
  constructor <;> linarith

theorem actual_minus_twice_log_delta_printed_rounding_and_false_exact_equality :
    |-2*Real.log (1/20)-(599/100:ℝ)|<1/200 ∧
      -2*Real.log (1/20)≠(599/100:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  constructor
  · rw [abs_lt];constructor <;> linarith
  · exact ne_of_gt (by linarith)

theorem exp_eighth_power_identity (value : ℝ) :
    Real.exp value=(Real.exp (value/8))^8 := by
  convert Real.exp_nat_mul (value/8) 8 using 1 <;> ring

theorem actual_log_one_hundred_one_decimal_enclosure :
    (46151/10000:ℝ)<Real.log 101 ∧ Real.log 101<(46152/10000:ℝ) := by
  have hlo := Real.exp_bound (x:=(46151/80000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  have hhi := Real.exp_bound (x:=(46152/80000:ℝ)) (by norm_num) (n:=16) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hlo hhi
  have helo : Real.exp (46151/80000:ℝ)≤1780488030/1000000000 := by
    have h := (abs_le.mp hlo).2
    linarith
  have hehi : (1780510284/1000000000:ℝ)≤Real.exp (46152/80000:ℝ) := by
    have h := (abs_le.mp hhi).1
    linarith
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<101)).mpr
    rw [exp_eighth_power_identity]
    have hp : (Real.exp (46151/80000:ℝ))^8≤(1780488030/1000000000:ℝ)^8 := by gcongr
    have hrat : (1780488030/1000000000:ℝ)^8<101 := by norm_num
    convert hp.trans_lt hrat using 1 <;> norm_num
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<101)).mpr
    rw [exp_eighth_power_identity]
    have hp : (1780510284/1000000000:ℝ)^8≤(Real.exp (46152/80000:ℝ))^8 := by gcongr
    have hrat : (101:ℝ)<(1780510284/1000000000:ℝ)^8 := by norm_num
    convert hrat.trans_le hp using 1 <;> norm_num

theorem actual_log_one_hundred_one_printed_rounding_and_false_exact_equality :
    |Real.log 101-(462/100:ℝ)|<1/200 ∧ Real.log 101≠(462/100:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_log_one_hundred_one_decimal_enclosure
  constructor
  · rw [abs_lt];constructor <;> linarith
  · exact ne_of_lt (by linarith)

theorem actual_original_noise_decimal_enclosure :
    (25854615/100000000:ℝ)<originalNoise ∧ originalNoise<(25854617/100000000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  have ht := Real.log_two_gt_d9
  have hb := Real.log_two_lt_d9
  have hp : 0≤Real.log 2-2*Real.log (1/20) := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (Real.log 2-2*Real.log (1/20))
  unfold originalNoise
  constructor <;> nlinarith

theorem actual_corrected_noise_decimal_enclosure :
    (325677/100000:ℝ)<correctedNoise ∧ correctedNoise<(325680/100000:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  obtain ⟨ht,hb⟩ := actual_log_one_hundred_one_decimal_enclosure
  have hp : 0≤Real.log 101-2*Real.log (1/20) := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (Real.log 101-2*Real.log (1/20))
  unfold correctedNoise
  constructor <;> nlinarith

theorem actual_original_and_corrected_noise_printed_two_decimal_roundings :
    |originalNoise-(26/100:ℝ)|<1/200 ∧ |correctedNoise-(326/100:ℝ)|<1/200 := by
  obtain ⟨hl,hu⟩ := actual_original_noise_decimal_enclosure
  obtain ⟨ht,hb⟩ := actual_corrected_noise_decimal_enclosure
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_noise_ratio_decimal_enclosure :
    (1259/100:ℝ)<correctedNoise/originalNoise ∧
      correctedNoise/originalNoise<(1260/100:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_original_noise_decimal_enclosure
  obtain ⟨ht,hb⟩ := actual_corrected_noise_decimal_enclosure
  have hp : 0<originalNoise := by linarith
  constructor
  · rw [lt_div_iff₀ hp];linarith
  · rw [div_lt_iff₀ hp];linarith

theorem actual_noise_ratio_printed_one_decimal_rounding :
    |correctedNoise/originalNoise-(126/10:ℝ)|<1/20 := by
  obtain ⟨hl,hu⟩ := actual_noise_ratio_decimal_enclosure
  rw [abs_lt];constructor <;> linarith

theorem actual_noise_formulas_at_the_literal_exercise_parameters :
    originalNoise=(1/10)*Real.sqrt (Real.log (1+1)-2*Real.log (1/20)) ∧
      correctedNoise=((1/10)/Real.sqrt (1/100))*
        Real.sqrt (Real.log (1+1/(1/100:ℝ))-2*Real.log (1/20)) := by
  have hs : Real.sqrt (1/100:ℝ)=1/10 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  norm_num [originalNoise,correctedNoise,hs]

theorem actual_radicands_are_not_the_printed_exact_decimal_substitutions :
    Real.log 2-2*Real.log (1/20)≠(668/100:ℝ) ∧
      Real.log 101-2*Real.log (1/20)≠(1061/100:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_minus_twice_log_delta_decimal_enclosure
  obtain ⟨ht,hb⟩ := actual_log_one_hundred_one_decimal_enclosure
  have htwo := Real.log_two_gt_d9
  constructor
  · exact ne_of_gt (by linarith)
  · exact ne_of_lt (by linarith)

end SafeLearning.CompleteModulesGPCorrectionNumerics
