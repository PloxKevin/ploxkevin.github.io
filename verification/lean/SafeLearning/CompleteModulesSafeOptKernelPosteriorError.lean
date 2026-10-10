import SafeLearning.CompleteModulesSafeOptRKHSPosteriorError

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesSafeOptKernelPosteriorError

open CompleteModulesKernel CompleteModulesGramBridge CompleteModulesSafeOptRKHSPosteriorError
open CompleteModulesSafeOptGPInformationBudget

variable {X : Type*}

def actualKernelCrossAt (kernel : X → X → ℝ) (query : ℕ → X) (t : ℕ) (x : X) : Fin t → ℝ :=
  fun i => kernel x (query i)

def actualKernelMeanAt (kernel : X → X → ℝ) (lambda : ℝ) (query : ℕ → X)
    (f : X → ℝ) (noise : ℕ → ℝ) (t : ℕ) (x : X) : ℝ :=
  actualKernelCrossAt kernel query t x ⬝ᵥ
    ((lambda • 1 + actualKernelPastGram kernel query t)⁻¹ *ᵥ
      (fun i : Fin t => f (query i) + noise i))

def actualKernelVarianceAt (kernel : X → X → ℝ) (lambda : ℝ) (query : ℕ → X)
    (t : ℕ) (x : X) : ℝ :=
  kernel x x - actualKernelCrossAt kernel query t x ⬝ᵥ
    ((lambda • 1 + actualKernelPastGram kernel query t)⁻¹ *ᵥ actualKernelCrossAt kernel query t x)

def actualKernelNoiseQuadratic (kernel : X → X → ℝ) (lambda : ℝ)
    (query : ℕ → X) (noise : ℕ → ℝ) (t : ℕ) : ℝ :=
  (fun i : Fin t => noise i) ⬝ᵥ (actualKernelPastGram kernel query t *ᵥ
    ((lambda • 1 + actualKernelPastGram kernel query t)⁻¹ *ᵥ (fun i : Fin t => noise i)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype X] [DecidableEq X]

/-- Compatibility with the actual RKHS derives PSD for the full finite
kernel; no independent positivity or feature-model conclusion is assumed. -/
theorem actual_finite_rkhs_kernel_is_positive_semidefinite (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y) :
    (Matrix.of kernel).PosSemidef := by
  have hgram : Matrix.of kernel = featureGram (scalarSection (H := H)) := by
    ext x y
    exact hkernel x y
  rw [hgram]
  exact feature_gram_positive_semidefinite _

/-- The actual sequential kernel formulas inherit the deterministic bound
at every input and every finite sample count, including zero observations.
Its noise quadratic is computed from precisely the same repeated-query Gram
matrix and positive likelihood regularizer as its mean and variance. -/
theorem actual_finite_kernel_posterior_error_is_bounded_at_every_input_and_round
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (f : H) (noise : ℕ → ℝ) :
    ∀ t : ℕ, ∀ x : X,
      |f x - actualKernelMeanAt kernel lambda query (fun y => f y) noise t x| ≤
        (‖f‖ + Real.sqrt (actualKernelNoiseQuadratic kernel lambda query noise t) / Real.sqrt lambda) *
          Real.sqrt (actualKernelVarianceAt kernel lambda query t x) := by
  intro t x
  let input : Fin t → X := fun i => query i
  have hgram : actualGram (H := H) input = actualKernelPastGram kernel query t := by
    ext i j
    exact (hkernel (query i) (query j)).symm
  have hridge : CompleteModulesMatrixGP.ridgeMatrix (actualGram (H := H) input) lambda =
      lambda • 1 + actualKernelPastGram kernel query t := by
    rw [CompleteModulesMatrixGP.ridgeMatrix, hgram, add_comm]
  have hcross : (fun i : Fin t => scalarKernel (H := H) x (input i)) =
      actualKernelCrossAt kernel query t x := by
    ext i
    exact (hkernel x (query i)).symm
  have hmean : (actualMeanFunction (H := H) input (fun i => f (input i) + noise i) lambda) x =
      actualKernelMeanAt kernel lambda query (fun y => f y) noise t x := by
    rw [actual_mean_is_matrix_posterior]
    unfold CompleteModulesMatrixGP.posteriorMean actualKernelMeanAt
    rw [hridge, hcross]
  have hvariance : actualRKHSPosteriorVariance (H := H) input lambda x =
      actualKernelVarianceAt kernel lambda query t x := by
    unfold actualRKHSPosteriorVariance CompleteModulesMatrixGP.posteriorVariance actualKernelVarianceAt
    rw [hridge, hcross, ← hkernel x x]
  have hnoise : actualRKHSNoiseQuadratic (H := H) input lambda (fun i : Fin t => noise i) =
      actualKernelNoiseQuadratic kernel lambda query noise t := by
    unfold actualRKHSNoiseQuadratic actualKernelNoiseQuadratic
    rw [hridge, hgram]
  simpa only [hmean, hvariance, hnoise] using
    actual_rkhs_posterior_error_is_bounded_by_norm_and_self_normalized_noise
      input lambda hlambda f (fun i : Fin t => noise i) x

omit [Fintype X] [DecidableEq X] in
/-- The same kernel's cross convention gives exactly the previously derived
standard sequential posterior variance at its actual current query. -/
theorem actual_rkhs_kernel_variance_at_the_current_query_is_the_standard_sequential_variance
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (lambda : ℝ) (query : ℕ → X) (t : ℕ) :
    actualKernelVarianceAt kernel lambda query t (query t) =
      actualKernelSequentialVariance kernel lambda query t := by
  have hcross : actualKernelCrossAt kernel query t (query t) = actualKernelPastCross kernel query t := by
    ext i
    rw [actualKernelCrossAt, actualKernelPastCross, hkernel, hkernel]
    exact real_inner_comm _ _
  unfold actualKernelVarianceAt actualKernelSequentialVariance
  rw [hcross]

/-- Normalization supplies the actual current-query standard deviation's
unit bound from the derived PSD kernel; it is compatible with this error bound. -/
theorem actual_normalized_rkhs_kernel_current_query_standard_deviation_is_in_the_unit_interval
    (kernel : X → X → ℝ) (hkernel : ∀ x y, kernel x y = scalarKernel (H := H) x y)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda : ℝ) (hlambda : 0 < lambda)
    (query : ℕ → X) (t : ℕ) :
    (Real.sqrt (actualKernelVarianceAt kernel lambda query t (query t))) ^ 2 ∈ Set.Icc 0 1 := by
  rw [actual_rkhs_kernel_variance_at_the_current_query_is_the_standard_sequential_variance
    kernel hkernel lambda query t]
  have h := actual_normalized_finite_kernel_sequential_posterior_variance_is_in_the_unit_interval
    kernel (actual_finite_rkhs_kernel_is_positive_semidefinite kernel hkernel)
    hnormalized lambda hlambda query t
  rw [Real.sq_sqrt h.1]
  exact h

end SafeLearning.CompleteModulesSafeOptKernelPosteriorError
