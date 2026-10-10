import SafeLearning.CompleteModulesDynamics

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SafeLearning.CompleteModulesThermalNumbers
open CompleteModulesDynamics

theorem actual_sqrt_five_rational_enclosure :
    (2.23606797 : ℝ)<Real.sqrt 5 ∧ Real.sqrt 5<2.23606799 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hn:=Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem actual_source_startup_radius_rounding :
    |Real.sqrt (49/50:ℝ)-0.989949|<0.0000005 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤49/50)
  have hn:=Real.sqrt_nonneg (49/50:ℝ)
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem actual_source_one_update_coordinate_radius_rounding :
    |thermalGain*Real.sqrt (49/50:ℝ)-0.754147|<0.0000005 := by
  obtain ⟨hfiveL,hfiveU⟩:=actual_sqrt_five_rational_enclosure
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤49/50)
  have hn:=Real.sqrt_nonneg (49/50:ℝ)
  have hrL : (0.98994949:ℝ)<Real.sqrt (49/50:ℝ) := by nlinarith
  have hrU : Real.sqrt (49/50:ℝ)<0.98994950 := by nlinarith
  have hqL : (0.7618033985:ℝ)<thermalGain := by unfold thermalGain;linarith
  have hqU : thermalGain<(0.7618033995:ℝ) := by unfold thermalGain;linarith
  have hpL := mul_le_mul hqL.le hrL.le (by norm_num : (0:ℝ)≤0.98994949)
    thermal_gain_positive_lt_one.1.le
  have hpU := mul_le_mul hqU.le hrU.le (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤0.7618033995)
  apply abs_lt.mpr
  constructor <;> nlinarith [hpL,hpU]

theorem actual_source_disturbance_tube_radius_rounding :
    |(1/20)/(1-thermalGain)-0.209911|<0.0000005 := by
  obtain ⟨hfiveL,hfiveU⟩:=actual_sqrt_five_rational_enclosure
  have hd : 0<1-thermalGain := by linarith [thermal_gain_positive_lt_one.2]
  have hqL : (0.7618033985:ℝ)<thermalGain := by unfold thermalGain;linarith
  have hqU : thermalGain<(0.7618033995:ℝ) := by unfold thermalGain;linarith
  apply abs_lt.mpr
  constructor
  · have h : (0.2099105:ℝ)<(1/20)/(1-thermalGain) := by
      apply (lt_div_iff₀ hd).mpr
      nlinarith
    linarith
  · have h : (1/20)/(1-thermalGain)<(0.2099115:ℝ) := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    linarith

theorem actual_source_unit_disk_margin_rounding :
    |thermalGain+1/20-0.811803|<0.0000005 ∧ thermalGain+1/20≤1 := by
  obtain ⟨hl,hu⟩:=actual_sqrt_five_rational_enclosure
  refine ⟨?_,thermal_unit_disk_with_disturbance_budget⟩
  unfold thermalGain
  apply abs_lt.mpr
  constructor <;> linarith

end SafeLearning.CompleteModulesThermalNumbers
