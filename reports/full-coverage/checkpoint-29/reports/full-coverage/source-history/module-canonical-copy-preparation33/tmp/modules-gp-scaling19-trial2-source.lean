import SafeLearning.CompleteModulesMatrixGP
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPScaling
open CompleteModulesMatrixGP
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_positive_noise_makes_every_psd_ridge_matrix_invertible
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda : ℝ) (hlambda : 0 < lambda) :
    IsUnit (ridgeMatrix K lambda) := by
  have hd : (lambda • (1 : Matrix I I ℝ)).PosDef := by
    have he : lambda • (1 : Matrix I I ℝ)=diagonal (fun _ => lambda) := by
      ext i j
      by_cases hij : i=j
      · subst j;simp
      · simp [hij]
    rw [he]
    exact Matrix.PosDef.diagonal (fun _ => hlambda)
  exact (Matrix.PosDef.posSemidef_add hK hd).isUnit

theorem actual_scaling_the_kernel_and_noise_scales_the_entire_ridge_matrix
    (K : Matrix I I ℝ) (lambda c : ℝ) :
    ridgeMatrix (c • K) (c*lambda)=c • ridgeMatrix K lambda := by
  simp only [ridgeMatrix,smul_add,smul_smul]

theorem actual_positive_joint_scaling_gives_the_true_inverse_ridge_scaling
    (K : Matrix I I ℝ) (lambda c : ℝ) (hc : 0 < c)
    (hRidge : IsUnit (ridgeMatrix K lambda)) :
    (ridgeMatrix (c • K) (c*lambda))⁻¹=c⁻¹ • (ridgeMatrix K lambda)⁻¹ := by
  letI : Invertible c := invertibleOfNonzero hc.ne'
  rw [actual_scaling_the_kernel_and_noise_scales_the_entire_ridge_matrix]
  simpa only [invOf_eq_inv] using Matrix.inv_smul (A:=ridgeMatrix K lambda) c
    ((ridgeMatrix K lambda).isUnit_iff_isUnit_det.mp hRidge)

theorem actual_joint_kernel_noise_scaling_keeps_every_posterior_mean_unchanged
    (K : Matrix I I ℝ) (q y : I → ℝ) (lambda c : ℝ) (hc : 0 < c)
    (hRidge : IsUnit (ridgeMatrix K lambda)) :
    posteriorMean (c • K) (c • q) y (c*lambda)=posteriorMean K q y lambda := by
  unfold posteriorMean
  rw [actual_positive_joint_scaling_gives_the_true_inverse_ridge_scaling K lambda c hc hRidge,
    Matrix.smul_mulVec,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp

theorem actual_joint_kernel_noise_scaling_scales_every_posterior_variance
    (K : Matrix I I ℝ) (q : I → ℝ) (prior lambda c : ℝ) (hc : 0 < c)
    (hRidge : IsUnit (ridgeMatrix K lambda)) :
    posteriorVariance (c • K) (c • q) (c*prior) (c*lambda)=
      c*posteriorVariance K q prior lambda := by
  unfold posteriorVariance
  rw [actual_positive_joint_scaling_gives_the_true_inverse_ridge_scaling K lambda c hc hRidge,
    Matrix.smul_mulVec,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp <;> ring

theorem actual_joint_kernel_noise_scaling_keeps_the_normalized_information_matrix_unchanged
    (K : Matrix I I ℝ) (lambda c : ℝ) (hc : 0 < c) :
    1+(c*lambda)⁻¹ • (c • K)=1+lambda⁻¹ • K := by
  rw [smul_smul,_root_.mul_inv_rev]
  congr 2
  field_simp

theorem actual_sqrt_scaling_of_posterior_variance_is_the_source_width_scaling
    (variance c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (c*variance)=Real.sqrt c*Real.sqrt variance :=
  Real.sqrt_mul hc variance

theorem actual_corrected_small_noise_multiplier_has_exact_inverse_sqrt_scaling
    (B R A lambda c : ℝ) (hlambda : 0 < lambda) (hc : 0 < c) :
    B/Real.sqrt c+(R/Real.sqrt (c*lambda))*Real.sqrt A=
      (1/Real.sqrt c)*(B+(R/Real.sqrt lambda)*Real.sqrt A) := by
  rw [Real.sqrt_mul hc.le]
  ring

theorem actual_exact_inverse_sqrt_multiplier_scaling_keeps_the_band_width_unchanged
    (beta variance c : ℝ) (hc : 0 < c) :
    (beta/Real.sqrt c)*Real.sqrt (c*variance)=beta*Real.sqrt variance := by
  rw [Real.sqrt_mul hc.le]
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp

theorem actual_fixed_psd_kernel_scaled_to_zero_has_logdet_tending_to_zero
    (K : Matrix I I ℝ) :
    Tendsto (fun c : ℝ => Real.log (1+c • K).det) (𝓝 0) (𝓝 0) := by
  have hd : Tendsto (fun c : ℝ => (1+c • K).det) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun c : ℝ => (1+c • K).det) := by fun_prop
    simpa using hc.tendsto 0
  have hl := Real.continuousAt_log (by norm_num : (1:ℝ)≠0)
  simpa only [Function.comp_def,Real.log_one] using hl.tendsto.comp hd

theorem actual_original_scaled_noise_band_tends_to_zero_for_fixed_kernel
    (K : Matrix I I ℝ) (R delta variance : ℝ) :
    Tendsto (fun c : ℝ => R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta)*
      Real.sqrt (c*variance)) (𝓝 0) (𝓝 0) := by
  have hs : Tendsto (fun c : ℝ => R*Real.sqrt (Real.log (1+c • K).det-2*Real.log delta))
      (𝓝 0) (𝓝 (R*Real.sqrt (0-2*Real.log delta))) :=
    ((actual_fixed_psd_kernel_scaled_to_zero_has_logdet_tending_to_zero K).sub
      (tendsto_const_nhds (x:=2*Real.log delta))).sqrt.const_mul R
  have hv : Tendsto (fun c : ℝ => Real.sqrt (c*variance)) (𝓝 0) (𝓝 0) := by
    simpa only [mul_comm,zero_mul,Real.sqrt_zero] using
      (tendsto_id.const_mul variance).sqrt
  simpa using hs.mul hv

end SafeLearning.CompleteModulesGPScaling
