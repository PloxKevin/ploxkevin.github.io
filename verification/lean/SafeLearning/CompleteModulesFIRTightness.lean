import SafeLearning.CompleteModulesFIRGain

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesFIRTightness
open CompleteModulesFIRGain

theorem actual_parameterized_gain_is_tight_iff_alignment
    (gain storage angle : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=gain ↔
      |Real.sin angle| *Real.sqrt storage=|Real.cos angle| *Real.sqrt (gain^2-storage) := by
  have hg := actual_parameterized_gain_squared_gap gain storage angle hstorage hupper
  have hn : 0 ≤ |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle| := by positivity
  constructor
  · intro he
    rw [he] at hg
    have hz : (|Real.sin angle| *Real.sqrt storage-|Real.cos angle| *Real.sqrt (gain^2-storage))^2=0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro he
    have hz : |Real.sin angle| *Real.sqrt storage-|Real.cos angle| *Real.sqrt (gain^2-storage)=0 := sub_eq_zero.mpr he
    rw [hz] at hg
    nlinarith

theorem actual_alignment_iff_squared_source_weights
    (gain storage angle : ℝ) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    (|Real.sin angle| *Real.sqrt storage=|Real.cos angle| *Real.sqrt (gain^2-storage)) ↔
      Real.sin angle^2*storage=Real.cos angle^2*(gain^2-storage) := by
  constructor
  · intro he
    have hs := congrArg (fun value : ℝ => value^2) he
    simpa only [mul_pow,sq_abs,Real.sq_sqrt hstorage,Real.sq_sqrt (sub_nonneg.mpr hupper)] using hs
  · intro he
    have hs : (|Real.sin angle| *Real.sqrt storage)^2=(|Real.cos angle| *Real.sqrt (gain^2-storage))^2 := by
      simpa only [mul_pow,sq_abs,Real.sq_sqrt hstorage,Real.sq_sqrt (sub_nonneg.mpr hupper)] using he
    nlinarith [mul_nonneg (abs_nonneg (Real.sin angle)) (Real.sqrt_nonneg storage),
      mul_nonneg (abs_nonneg (Real.cos angle)) (Real.sqrt_nonneg (gain^2-storage))]

theorem actual_interior_parameterized_gain_tight_iff_source_tangent_ratio
    (gain storage angle : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 < storage) (hupper : storage < gain^2) :
    |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=gain ↔
      Real.tan angle^2=(gain^2-storage)/storage := by
  by_cases hcos : Real.cos angle=0
  · have hsin : Real.sin angle≠0 := by
      intro hz
      have ht := Real.sin_sq_add_cos_sq angle
      rw [hcos,hz] at ht
      norm_num at ht
    have hl : ¬(|actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=gain) := by
      rw [actual_parameterized_gain_is_tight_iff_alignment gain storage angle hgain hstorage.le hupper.le]
      have hp := mul_pos (abs_pos.mpr hsin) (Real.sqrt_pos.mpr hstorage)
      simp only [hcos,abs_zero,zero_mul]
      exact ne_of_gt hp
    have hr : 0 < (gain^2-storage)/storage := div_pos (sub_pos.mpr hupper) hstorage
    simp [hl,Real.tan_eq_sin_div_cos,hcos]
    exact ne_of_lt hr
  · rw [actual_parameterized_gain_is_tight_iff_alignment gain storage angle hgain hstorage.le hupper.le,
      actual_alignment_iff_squared_source_weights gain storage angle hstorage.le hupper.le,
      Real.tan_eq_sin_div_cos,div_pow,div_eq_div_iff (pow_ne_zero 2 hcos) hstorage.ne']
    rw [mul_comm (gain^2-storage)]

theorem actual_half_storage_quarter_pi_kernels_are_exactly_one_half :
    actualParameterizedCurrentKernel 1 (1/2) (Real.pi/4)=(1/2:ℝ) ∧
    actualParameterizedDelayedKernel (1/2) (Real.pi/4)=(1/2:ℝ) := by
  have hm : Real.sqrt 2*Real.sqrt (1/2)=1 := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  norm_num only [actualParameterizedCurrentKernel,actualParameterizedDelayedKernel,
    Real.sin_pi_div_four,Real.cos_pi_div_four,one_pow,show (1:ℝ)-1/2=1/2 by norm_num]
  constructor <;> nlinarith

theorem actual_half_storage_quarter_pi_frequency_gain_is_exactly_one :
    sSup (Set.range (fun frequency : ℝ => ‖actualFIRTransfer
      (actualParameterizedCurrentKernel 1 (1/2) (Real.pi/4))
      (actualParameterizedDelayedKernel (1/2) (Real.pi/4)) frequency‖))=(1:ℝ) := by
  rw [actual_half_storage_quarter_pi_kernels_are_exactly_one_half.1,
    actual_half_storage_quarter_pi_kernels_are_exactly_one_half.2,
    actual_positive_fir_frequency_supremum (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

end SafeLearning.CompleteModulesFIRTightness
