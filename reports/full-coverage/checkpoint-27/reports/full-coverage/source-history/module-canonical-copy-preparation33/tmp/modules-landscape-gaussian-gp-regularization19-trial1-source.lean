import SafeLearning.CompleteModulesSafeOptPosteriorError
import SafeLearning.CompleteModulesSafeOptFiniteInformationBound

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeGaussianGPRegularization
open Matrix
open scoped NNReal BigOperators
open CompleteFoundationsSequentialLogDet CompleteModulesSafeOptPosteriorError
  CompleteModulesSafeOptFiniteInformationBound

/-- The actual Gaussian prior variance that matches noise scale R and GP
regularization lambda. -/
def actualGPIsotropicPriorVariance (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) : ℝ≥0 :=
  ⟨1 / (R ^ 2 * lambda), by positivity⟩

theorem actual_gp_isotropic_prior_variance_is_positive
    (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    0 < actualGPIsotropicPriorVariance R lambda hR hlambda := by
  apply NNReal.coe_pos.mp
  change 0 < 1 / (R ^ 2 * lambda)
  positivity

/-- The prior cancels the actual squared noise scale, yielding the true GP
normalized matrix. This algebra is valid even before any PSD hypothesis. -/
theorem actual_gp_prior_normalization_is_the_actual_normalized_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) • (R ^ 2 • G) =
      1 + lambda⁻¹ • G := by
  have hs : (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) * R ^ 2 = lambda⁻¹ := by
    change 1 / (R ^ 2 * lambda) * R ^ 2 = lambda⁻¹
    field_simp
  rw [smul_smul, hs]

theorem actual_gp_prior_normalized_determinant_is_the_actual_normalized_determinant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    (1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) • (R ^ 2 • G)).det =
      (1 + lambda⁻¹ • G).det := by
  rw [actual_gp_prior_normalization_is_the_actual_normalized_matrix G R lambda hR hlambda]

/-- PSD derives nonsingularity internally, and the actual normalized inverse
is lambda times the GP regularized inverse. -/
theorem actual_gp_normalized_inverse_is_lambda_times_the_regularized_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (lambda : ℝ) (hlambda : 0 < lambda) :
    (1 + lambda⁻¹ • G)⁻¹ = lambda • (lambda • 1 + G)⁻¹ := by
  have hd := (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    G hG lambda⁻¹ (inv_nonneg.mpr hlambda.le)).2
  have hu : IsUnit (1 + lambda⁻¹ • G).det := isUnit_iff_ne_zero.mpr (by linarith)
  have hs : lambda • 1 + G = lambda • (1 + lambda⁻¹ • G) := by
    simp [smul_add, smul_smul, mul_inv_cancel₀ hlambda.ne']
  letI : Invertible lambda := invertibleOfNonzero hlambda.ne'
  rw [hs, Matrix.inv_smul _ lambda hu]
  simp [invOf_eq_inv, smul_smul, mul_inv_cancel₀ hlambda.ne']

/-- Exact prior self-normalization equals the actual GP regularized noise
quadratic divided by the squared noise scale. -/
theorem actual_gp_scaled_prior_quadratic_is_the_actual_regularized_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (S : ι → ℝ)
    (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) *
      (S ⬝ᵥ ((1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) • (R ^ 2 • G))⁻¹ *ᵥ S)) =
      (1 / R ^ 2) * (S ⬝ᵥ ((lambda • 1 + G)⁻¹ *ᵥ S)) := by
  rw [actual_gp_prior_normalization_is_the_actual_normalized_matrix G R lambda hR hlambda,
    actual_gp_normalized_inverse_is_lambda_times_the_regularized_inverse G hG lambda hlambda,
    Matrix.smul_mulVec, dotProduct_smul]
  change (1 / (R ^ 2 * lambda)) * (lambda * _) = (1 / R ^ 2) * _
  field_simp

variable {sample feature : Type*} [Fintype sample] [Fintype feature]
  [DecidableEq sample] [DecidableEq feature]

/-- Actual finite-feature S=Phi^T epsilon and G=Phi^T Phi give the actual
kernel quadratic, using the protected exact pushthrough identity. -/
theorem actual_gp_feature_prior_quadratic_is_the_actual_kernel_noise_quadratic
    (Phi : Matrix sample feature ℝ) (noise : sample → ℝ)
    (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) *
      ((Phiᵀ *ᵥ noise) ⬝ᵥ
        ((1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) •
          (R ^ 2 • featureGram Phi))⁻¹ *ᵥ (Phiᵀ *ᵥ noise))) =
      (1 / R ^ 2) * (noise ⬝ᵥ (kernelGram Phi *ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ noise))) := by
  have hG : (featureGram Phi).PosSemidef := by
    simpa only [featureGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Phi
  rw [actual_gp_scaled_prior_quadratic_is_the_actual_regularized_quadratic
    (featureGram Phi) hG (Phiᵀ *ᵥ noise) R lambda hR hlambda]
  change (1 / R ^ 2) * actualFeatureNoiseQuadratic lambda Phi noise = _
  rw [actual_feature_noise_quadratic_is_the_kernel_noise_quadratic lambda hlambda Phi noise]

/-- The true feature prior determinant equals the actual normalized kernel
determinant, even with repeated or linearly dependent feature rows. -/
theorem actual_gp_feature_prior_determinant_is_the_actual_kernel_normalized_determinant
    (Phi : Matrix sample feature ℝ) (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    (1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) •
      (R ^ 2 • featureGram Phi)).det = (1 + lambda⁻¹ • kernelGram Phi).det := by
  rw [actual_gp_prior_normalized_determinant_is_the_actual_normalized_determinant
    (featureGram Phi) R lambda hR hlambda]
  simpa only [featureGram, kernelGram, Matrix.smul_mul, Matrix.mul_smul] using
    (CompleteFoundationsUniversalMatrices.actual_sylvester_determinant_identity (lambda⁻¹ • Phi) Phiᵀ).symm

/-- The exact determinant/exponential expression computed by Gaussian
integration translates to the actual GP kernel regularization expression. -/
theorem actual_gp_feature_gaussian_value_is_the_actual_kernel_gaussian_value
    (Phi : Matrix sample feature ℝ) (noise : sample → ℝ)
    (R lambda : ℝ) (hR : 0 < R) (hlambda : 0 < lambda) :
    (Real.sqrt (1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) •
      (R ^ 2 • featureGram Phi)).det)⁻¹ *
      Real.exp ((actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) / 2 *
        ((Phiᵀ *ᵥ noise) ⬝ᵥ ((1 + (actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) •
          (R ^ 2 • featureGram Phi))⁻¹ *ᵥ (Phiᵀ *ᵥ noise)))) =
    (Real.sqrt (1 + lambda⁻¹ • kernelGram Phi).det)⁻¹ *
      Real.exp ((noise ⬝ᵥ (kernelGram Phi *ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ noise))) / (2 * R ^ 2)) := by
  rw [actual_gp_feature_prior_determinant_is_the_actual_kernel_normalized_determinant
    Phi R lambda hR hlambda]
  congr 2
  have hq := actual_gp_feature_prior_quadratic_is_the_actual_kernel_noise_quadratic
    Phi noise R lambda hR hlambda
  calc
    _ = ((actualGPIsotropicPriorVariance R lambda hR hlambda : ℝ) * _) / 2 := by ring
    _ = _ := by rw [hq]; ring

end SafeLearning.CompleteModulesLandscapeGaussianGPRegularization
