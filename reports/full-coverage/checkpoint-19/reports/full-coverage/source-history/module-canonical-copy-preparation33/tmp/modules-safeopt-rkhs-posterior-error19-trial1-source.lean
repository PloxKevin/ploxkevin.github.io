import SafeLearning.CompleteModulesSafeOptPosteriorError
import SafeLearning.CompleteModulesGramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesSafeOptRKHSPosteriorError

open CompleteModulesKernel CompleteModulesGramBridge
open CompleteFoundationsSequentialLogDet CompleteModulesSafeOptPosteriorError

variable {H X sample : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype X]

/-- Evaluation on the entire finite domain is injective. Thus the actual
RKHS, including a degenerate zero-dimensional one, is finite-dimensional. -/
theorem actual_finite_domain_rkhs_is_finite_dimensional : FiniteDimensional ℝ H := by
  exact FiniteDimensional.of_injective (RKHS.coeCLM ℝ : H →L[ℝ] X → ℝ).toLinearMap
    (RKHS.coeCLM_injective (𝕜 := ℝ) (H := H))

/-- An orthonormal coordinate model preserves the actual kernel, every
true function value, and its actual RKHS norm. No sample independence or
strictly positive definite kernel is required. -/
theorem actual_finite_domain_rkhs_has_norm_preserving_real_features (f : H) :
    ∃ features : X → Fin (Module.finrank ℝ H) → ℝ,
      ∃ theta : Fin (Module.finrank ℝ H) → ℝ,
        (∀ x y, scalarKernel (H := H) x y = features x ⬝ᵥ features y) ∧
        (∀ x, f x = features x ⬝ᵥ theta) ∧ Real.sqrt (theta ⬝ᵥ theta) = ‖f‖ := by
  letI := actual_finite_domain_rkhs_is_finite_dimensional (H := H) (X := X)
  let b := stdOrthonormalBasis ℝ H
  let features : X → Fin (Module.finrank ℝ H) → ℝ :=
    fun x j => inner ℝ (scalarSection (H := H) x) (b j)
  let theta : Fin (Module.finrank ℝ H) → ℝ := fun j => inner ℝ (b j) f
  refine ⟨features, theta, ?_, ?_, ?_⟩
  · intro x y
    unfold scalarKernel featureKernel
    rw [← b.sum_inner_mul_inner (scalarSection (H := H) x) (scalarSection (H := H) y)]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [features]
    rw [real_inner_comm (b j)]
  · intro x
    rw [← scalar_section_reproduces, real_inner_comm f,
      ← b.sum_inner_mul_inner (scalarSection (H := H) x) f]
    rfl
  · have hnorm : theta ⬝ᵥ theta = ‖f‖ ^ 2 := by
      simpa only [dotProduct, theta, ← pow_two] using b.sum_sq_inner_right f
    rw [hnorm, Real.sqrt_sq (norm_nonneg f)]

variable [Fintype sample] [DecidableEq sample]

def actualRKHSNoiseQuadratic (input : sample → X) (lambda : ℝ) (noise : sample → ℝ) : ℝ :=
  noise ⬝ᵥ (actualGram (H := H) input *ᵥ
    ((CompleteModulesMatrixGP.ridgeMatrix (actualGram (H := H) input) lambda)⁻¹ *ᵥ noise))

def actualRKHSPosteriorVariance (input : sample → X) (lambda : ℝ) (x : X) : ℝ :=
  CompleteModulesMatrixGP.posteriorVariance (actualGram (H := H) input)
    (fun i => scalarKernel (H := H) x (input i)) (scalarKernel (H := H) x x) lambda

/-- Actual matrix/RKHS posterior error is bounded by the actual RKHS norm
plus the actual self-normalized observed noise, times the true posterior
standard deviation. This is deterministic, for every query and any repeated
sample inputs; it contains no assumed confidence inequality or probability. -/
theorem actual_rkhs_posterior_error_is_bounded_by_norm_and_self_normalized_noise
    (input : sample → X) (lambda : ℝ) (hlambda : 0 < lambda) (f : H)
    (noise : sample → ℝ) (x : X) :
    |f x - (actualMeanFunction (H := H) input (fun i => f (input i) + noise i) lambda) x| ≤
      (‖f‖ + Real.sqrt (actualRKHSNoiseQuadratic (H := H) input lambda noise) / Real.sqrt lambda) *
        Real.sqrt (actualRKHSPosteriorVariance (H := H) input lambda x) := by
  classical
  obtain ⟨features, theta, hkernel, hf, hnorm⟩ :=
    actual_finite_domain_rkhs_has_norm_preserving_real_features f
  let Phi : Matrix sample (Fin (Module.finrank ℝ H)) ℝ := fun i j => features (input i) j
  let phi := features x
  have hgram : kernelGram Phi = actualGram (H := H) input := by
    ext i j
    simpa only [kernelGram, Matrix.mul_apply, Matrix.transpose_apply, Phi, dotProduct,
      actual_gram_entry] using (hkernel (input i) (input j)).symm
  have hcross : Phi *ᵥ phi = fun i => scalarKernel (H := H) x (input i) := by
    ext i
    change features (input i) ⬝ᵥ features x = scalarKernel (H := H) x (input i)
    rw [dotProduct_comm, ← hkernel]
  have htrue : Phi *ᵥ theta = fun i => f (input i) := by
    ext i
    exact (hf (input i)).symm
  have hquery : phi ⬝ᵥ theta = f x := (hf x).symm
  have hridge : noisyKernel lambda Phi =
      CompleteModulesMatrixGP.ridgeMatrix (actualGram (H := H) input) lambda := by
    rw [noisyKernel, hgram, CompleteModulesMatrixGP.ridgeMatrix, add_comm]
  have hvariance : posteriorVariance lambda Phi phi =
      actualRKHSPosteriorVariance (H := H) input lambda x := by
    unfold posteriorVariance actualRKHSPosteriorVariance CompleteModulesMatrixGP.posteriorVariance
    rw [hcross, hridge]
    exact congrArg (fun v => v - _) (hkernel x x).symm
  have hnoise : actualFeatureNoiseQuadratic lambda Phi noise =
      actualRKHSNoiseQuadratic (H := H) input lambda noise := by
    rw [actual_feature_noise_quadratic_is_the_kernel_noise_quadratic lambda hlambda Phi noise,
      hgram, hridge]
    rfl
  have hmean : actualFeaturePosteriorMean lambda Phi phi (Phi *ᵥ theta + noise) =
      (actualMeanFunction (H := H) input (fun i => f (input i) + noise i) lambda) x := by
    rw [actual_mean_is_matrix_posterior]
    unfold actualFeaturePosteriorMean CompleteModulesMatrixGP.posteriorMean
    rw [hcross, hridge, htrue]
    rfl
  have h := actual_feature_posterior_error_is_bounded_by_norm_and_self_normalized_noise
    lambda hlambda Phi phi theta noise
  simpa only [hquery, hmean, hnoise, hvariance, hnorm] using h

/-- Primitive bounds on the norm and self-normalized noise imply an actual
uniform-in-input deterministic band for this dataset. They are scalar norm
bounds, not an assumed posterior confidence inequality. -/
theorem actual_rkhs_norm_and_noise_bounds_give_every_input_a_posterior_band
    (input : sample → X) (lambda : ℝ) (hlambda : 0 < lambda) (f : H)
    (noise : sample → ℝ) (B S : ℝ) (hB : ‖f‖ ≤ B)
    (hS : Real.sqrt (actualRKHSNoiseQuadratic (H := H) input lambda noise) ≤ S) :
    ∀ x : X,
      |f x - (actualMeanFunction (H := H) input (fun i => f (input i) + noise i) lambda) x| ≤
        (B + S / Real.sqrt lambda) * Real.sqrt (actualRKHSPosteriorVariance (H := H) input lambda x) := by
  intro x
  apply (actual_rkhs_posterior_error_is_bounded_by_norm_and_self_normalized_noise
    input lambda hlambda f noise x).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact add_le_add hB (div_le_div_of_nonneg_right hS (Real.sqrt_nonneg _))

end SafeLearning.CompleteModulesSafeOptRKHSPosteriorError
