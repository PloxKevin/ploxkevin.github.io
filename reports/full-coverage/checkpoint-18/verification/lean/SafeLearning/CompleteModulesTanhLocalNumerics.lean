import SafeLearning.CompleteModulesTanhNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SafeLearning.CompleteModulesTanhLocalNumerics
open CompleteModulesTanhNumerics

theorem actual_tanh_two_rigorous_rational_enclosure :
    (0.96402757:ℝ) < Real.tanh 2 ∧ Real.tanh 2 < 0.96402759 := by
  have he : Real.exp (2:ℝ) = (Real.exp 1)^2 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    ring
  have hl := Real.exp_one_gt_d9
  have hu := Real.exp_one_lt_d9
  have hn := Real.exp_pos 1
  have hsqL : (7.389056097:ℝ) < (Real.exp 1)^2 := by nlinarith
  have hsqU : (Real.exp 1)^2 < (7.389056100:ℝ) := by nlinarith
  have hfourL : (54.59815000:ℝ) < (Real.exp 2)^2 := by rw [he]; nlinarith
  have hfourU : (Real.exp 2)^2 < (54.59815007:ℝ) := by rw [he]; nlinarith
  rw [actual_tanh_is_the_exponential_square_ratio]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < (Real.exp 2)^2+1)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < (Real.exp 2)^2+1)).mpr
    nlinarith

theorem actual_source_local_origin_and_derivative_bounds_at_two_rounding :
    |Real.tanh 2/2-0.482| < (0.0005:ℝ) ∧
    |(1-(Real.tanh 2)^2)-0.071| < 0.0005 ∧
    |(1-(Real.tanh 2)^2)-0.0707| < 0.00005 ∧
    1-(Real.tanh 2)^2 < Real.tanh 2/2 := by
  have hl := actual_tanh_two_rigorous_rational_enclosure.1
  have hu := actual_tanh_two_rigorous_rational_enclosure.2
  refine ⟨?_,?_,?_,?_⟩
  · apply abs_lt.mpr; constructor <;> linarith
  · apply abs_lt.mpr; constructor <;> nlinarith
  · apply abs_lt.mpr; constructor <;> nlinarith
  · nlinarith

theorem actual_source_precise_origin_sector_and_slope_values_at_one_rounding :
    |Real.tanh 1-0.76159416| < (0.000000005:ℝ) ∧
    |(1-(Real.tanh 1)^2)-0.41997434| < 0.000000005 ∧
    |2*Real.tanh 1*(1-Real.tanh 1)-0.363137| < 0.0000005 ∧
    0 < 2*Real.tanh 1*(1-Real.tanh 1) := by
  have hl := actual_tanh_one_rigorous_rational_enclosure.1
  have hu := actual_tanh_one_rigorous_rational_enclosure.2
  refine ⟨?_,?_,?_,?_⟩
  · apply abs_lt.mpr; constructor <;> linarith
  · apply abs_lt.mpr; constructor <;> nlinarith
  · apply abs_lt.mpr; constructor <;> nlinarith
  · nlinarith

end SafeLearning.CompleteModulesTanhLocalNumerics
