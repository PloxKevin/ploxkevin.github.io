import SafeLearning.CompleteModulesFIRTightness
import SafeLearning.CompleteModulesFIRBase

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesFIRBoundaryTightness
open CompleteModulesFIRGain CompleteModulesFIRTightness CompleteModulesFIRBase

theorem actual_nonnegative_regularizer_storage_is_positive_and_at_most_gain_squared
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain) (hregularizer : 0 ≤ regularizer) :
    0 < actualFIRStorage gain freeParameter regularizer ∧
      actualFIRStorage gain freeParameter regularizer ≤ gain^2 := by
  rw [actual_fir_inverse_gramian_storage_formula gain freeParameter regularizer hgain hregularizer]
  have hg : 0 < gain^2 := sq_pos_of_pos hgain
  have hd : 0 < 1+gain^2*(freeParameter^2+regularizer) := by positivity
  constructor
  · positivity
  · rw [div_le_iff₀ hd]
    nlinarith [mul_nonneg (sq_nonneg gain) (add_nonneg (sq_nonneg freeParameter) hregularizer)]

/-- The source tangent equation also holds at the allowed semidefinite storage
endpoint, on the ordinary domain where tangent has nonzero cosine. -/
theorem actual_defined_tangent_parameterized_gain_tight_iff
    (gain storage angle : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 < storage)
    (hupper : storage ≤ gain^2) (hcos : Real.cos angle≠0) :
    |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=gain ↔
      Real.tan angle^2=(gain^2-storage)/storage := by
  rw [actual_parameterized_gain_is_tight_iff_alignment gain storage angle hgain hstorage.le hupper,
    actual_alignment_iff_squared_source_weights gain storage angle hstorage.le hupper,
    Real.tan_eq_sin_div_cos,div_pow,div_eq_div_iff (pow_ne_zero 2 hcos) hstorage.ne']
  rw [mul_comm (gain^2-storage)]

theorem actual_endpoint_parameterized_gain_tight_iff_sine_zero
    (gain angle : ℝ) (hgain : 0 < gain) :
    |actualParameterizedCurrentKernel gain (gain^2) angle|+
      |actualParameterizedDelayedKernel (gain^2) angle|=gain ↔ Real.sin angle=0 := by
  rw [actual_parameterized_gain_is_tight_iff_alignment gain (gain^2) angle hgain.le (sq_nonneg gain) le_rfl,
    actual_alignment_iff_squared_source_weights gain (gain^2) angle (sq_nonneg gain) le_rfl]
  simp [mul_eq_zero,ne_of_gt (sq_pos_of_pos hgain)]

theorem actual_tight_positive_storage_has_defined_tangent
    (gain storage angle : ℝ) (hgain : 0 ≤ gain) (hstorage : 0 < storage)
    (hupper : storage ≤ gain^2)
    (htight : |actualParameterizedCurrentKernel gain storage angle|+|actualParameterizedDelayedKernel storage angle|=gain) :
    Real.cos angle≠0 := by
  intro hcos
  have he := (actual_parameterized_gain_is_tight_iff_alignment gain storage angle hgain hstorage.le hupper).mp htight
  have hsin : Real.sin angle≠0 := by
    intro hz
    have ht := Real.sin_sq_add_cos_sq angle
    rw [hz,hcos] at ht
    norm_num at ht
  have hp := mul_pos (abs_pos.mpr hsin) (Real.sqrt_pos.mpr hstorage)
  simp only [hcos,abs_zero,zero_mul] at he
  linarith

end SafeLearning.CompleteModulesFIRBoundaryTightness
