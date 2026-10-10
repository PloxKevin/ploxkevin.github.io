import SafeLearning.CompleteModulesGPScaling
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesGPScalingConsequences
open CompleteModulesGPScaling
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_original_full_band_is_the_fixed_bias_band_plus_the_shrinking_noise_band
    (K : Matrix I I ℝ) (B R delta variance c : ℝ) (hc : 0 < c) :
    (B/Real.sqrt c+R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta))*
      Real.sqrt (c*variance)=
        B*Real.sqrt variance+R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta)*
          Real.sqrt (c*variance) := by
  rw [add_mul,actual_exact_inverse_sqrt_multiplier_scaling_keeps_the_band_width_unchanged
    B variance c hc]

theorem actual_original_full_band_tends_to_the_true_bias_band_under_positive_rescaling
    (K : Matrix I I ℝ) (B R delta variance : ℝ) :
    Tendsto (fun c : ℝ =>
      (B/Real.sqrt c+R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta))*
        Real.sqrt (c*variance)) (𝓝[>] 0) (𝓝 (B*Real.sqrt variance)) := by
  have ht := ((actual_original_scaled_noise_band_tends_to_zero_for_fixed_kernel
    K R delta variance).mono_left
      (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ)) ≤ 𝓝 0)).const_add (B*Real.sqrt variance)
  have he : (fun c : ℝ =>
      B*Real.sqrt variance+R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta)*
        Real.sqrt (c*variance)) =ᶠ[𝓝[>] 0]
      (fun c : ℝ =>
        (B/Real.sqrt c+R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta))*
          Real.sqrt (c*variance)) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (actual_original_full_band_is_the_fixed_bias_band_plus_the_shrinking_noise_band
      K B R delta variance c hc).symm
  simpa only [add_zero] using ht.congr' he

end SafeLearning.CompleteModulesGPScalingConsequences
