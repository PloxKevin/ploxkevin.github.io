import SafeLearning.CompleteModulesSafeOptGPInformationBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesSafeOptPosteriorError

open CompleteFoundationsSequentialLogDet CompleteModulesSafeOptGPInformationBudget

variable {sample feature : Type*} [Fintype sample] [Fintype feature]
  [DecidableEq sample] [DecidableEq feature]

def actualFeaturePosteriorMean (lambda : ℝ) (Phi : Matrix sample feature ℝ)
    (phi : feature → ℝ) (labels : sample → ℝ) : ℝ :=
  (Phi *ᵥ phi) ⬝ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ labels)

def actualFeatureNoiseQuadratic (lambda : ℝ) (Phi : Matrix sample feature ℝ)
    (noise : sample → ℝ) : ℝ :=
  (Phiᵀ *ᵥ noise) ⬝ᵥ ((featureCovariance lambda Phi)⁻¹ *ᵥ (Phiᵀ *ᵥ noise))

/-- The two actual inverse systems give the same finite-feature posterior mean. -/
theorem actual_regularized_inverse_pushthrough (lambda : ℝ) (hlambda : 0 < lambda)
    (Phi : Matrix sample feature ℝ) :
    (featureCovariance lambda Phi)⁻¹ * Phiᵀ = Phiᵀ * (noisyKernel lambda Phi)⁻¹ := by
  have hi := actual_regularized_feature_and_kernel_invertible lambda hlambda Phi
  have h := congrArg (fun M : Matrix feature sample ℝ =>
    (featureCovariance lambda Phi)⁻¹ * M * (noisyKernel lambda Phi)⁻¹)
    (actual_feature_kernel_pushthrough lambda Phi)
  simp only [← Matrix.mul_assoc] at h
  rw [Matrix.nonsing_inv_mul _ hi.2.1, Matrix.one_mul,
    Matrix.mul_assoc ((featureCovariance lambda Phi)⁻¹ * Phiᵀ),
    Matrix.mul_nonsing_inv _ hi.2.2.2, Matrix.mul_one] at h
  exact h.symm

/-- Observed labels are the true feature values plus their actual noise.
The error splits into regularization bias and the weighted observed noise. -/
theorem actual_feature_posterior_error_is_bias_minus_weighted_noise
    (lambda : ℝ) (hlambda : 0 < lambda) (Phi : Matrix sample feature ℝ)
    (phi theta : feature → ℝ) (noise : sample → ℝ) :
    phi ⬝ᵥ theta - actualFeaturePosteriorMean lambda Phi phi (Phi *ᵥ theta + noise) =
      lambda * (phi ⬝ᵥ ((featureCovariance lambda Phi)⁻¹ *ᵥ theta)) -
        phi ⬝ᵥ ((featureCovariance lambda Phi)⁻¹ *ᵥ (Phiᵀ *ᵥ noise)) := by
  have hi := actual_regularized_feature_and_kernel_invertible lambda hlambda Phi
  have hprod : (featureCovariance lambda Phi)⁻¹ * featureGram Phi =
      1 - lambda • (featureCovariance lambda Phi)⁻¹ := by
    have h := Matrix.nonsing_inv_mul (featureCovariance lambda Phi) hi.2.1
    rw [featureCovariance, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
    exact eq_sub_of_add_eq' h
  have hm : actualFeaturePosteriorMean lambda Phi phi (Phi *ᵥ theta + noise) =
      phi ⬝ᵥ ((featureCovariance lambda Phi)⁻¹ *ᵥ (Phiᵀ *ᵥ (Phi *ᵥ theta + noise))) := by
    unfold actualFeaturePosteriorMean
    rw [Matrix.mulVec_mulVec, actual_regularized_inverse_pushthrough lambda hlambda Phi,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hm, Matrix.mulVec_add, Matrix.mulVec_add, dotProduct_add,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  change phi ⬝ᵥ theta -
    (phi ⬝ᵥ (((featureCovariance lambda Phi)⁻¹ * featureGram Phi) *ᵥ theta) + _) = _
  rw [hprod, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul]
  ring

/-- The feature self-normalized noise is exactly the standard kernel
quadratic, including singular Gram matrices and repeated observations. -/
theorem actual_feature_noise_quadratic_is_the_kernel_noise_quadratic
    (lambda : ℝ) (hlambda : 0 < lambda) (Phi : Matrix sample feature ℝ)
    (noise : sample → ℝ) :
    actualFeatureNoiseQuadratic lambda Phi noise =
      noise ⬝ᵥ (kernelGram Phi *ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ noise)) := by
  unfold actualFeatureNoiseQuadratic
  rw [Matrix.mulVec_mulVec, actual_regularized_inverse_pushthrough lambda hlambda Phi,
    ← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec]
  rfl

private theorem actual_positive_definite_bilinear_sqrt_bound
    {index : Type*} [Fintype index] (A : Matrix index index ℝ) (hA : A.PosDef)
    (x y : index → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ Real.sqrt (x ⬝ᵥ (A *ᵥ x)) * Real.sqrt (y ⬝ᵥ (A *ᵥ y)) := by
  have hx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by
    simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg y
  have hcs := hA.star_dotProduct_mulVec_mul_le x y
  simp only [star_trivial] at hcs
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hsq : (|x ⬝ᵥ (A *ᵥ y)|) ^ 2 ≤
      (Real.sqrt (x ⬝ᵥ (A *ᵥ x)) * Real.sqrt (y ⬝ᵥ (A *ᵥ y))) ^ 2 := by
    rw [sq_abs, mul_pow, hsx, hsy]
    simpa only [pow_two] using hcs
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- A true deterministic posterior-standard-deviation error bound, derived
from the actual feature norm and the actual self-normalized observed noise. -/
theorem actual_feature_posterior_error_is_bounded_by_norm_and_self_normalized_noise
    (lambda : ℝ) (hlambda : 0 < lambda) (Phi : Matrix sample feature ℝ)
    (phi theta : feature → ℝ) (noise : sample → ℝ) :
    |phi ⬝ᵥ theta - actualFeaturePosteriorMean lambda Phi phi (Phi *ᵥ theta + noise)| ≤
      (Real.sqrt (theta ⬝ᵥ theta) +
        Real.sqrt (actualFeatureNoiseQuadratic lambda Phi noise) / Real.sqrt lambda) *
          Real.sqrt (posteriorVariance lambda Phi phi) := by
  let A := (featureCovariance lambda Phi)⁻¹
  let v := posteriorVariance lambda Phi phi
  have hi := actual_regularized_feature_and_kernel_invertible lambda hlambda Phi
  have hp := actual_regularized_finite_feature_posterior_variance_lies_between_zero_and_the_prior
    lambda hlambda Phi phi
  have ht := actual_regularized_finite_feature_posterior_variance_lies_between_zero_and_the_prior
    lambda hlambda Phi theta
  have hq : phi ⬝ᵥ (A *ᵥ phi) = v / lambda :=
    actual_posterior_variance_equals_feature_inverse lambda hlambda Phi phi
  have hqt : lambda * (theta ⬝ᵥ (A *ᵥ theta)) ≤ theta ⬝ᵥ theta := by
    rw [actual_posterior_variance_equals_feature_inverse lambda hlambda Phi theta]
    simpa only [mul_div_cancel₀ _ hlambda.ne'] using ht.2
  have htheta : 0 ≤ theta ⬝ᵥ (A *ᵥ theta) := by
    simpa only [star_trivial] using hi.1.inv.posSemidef.dotProduct_mulVec_nonneg theta
  have hroot : Real.sqrt (phi ⬝ᵥ (A *ᵥ phi)) = Real.sqrt v / Real.sqrt lambda := by
    rw [hq, Real.sqrt_div hp.1]
  have hbiassqrt : lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) / Real.sqrt lambda ≤
      Real.sqrt (theta ⬝ᵥ theta) := by
    have hll := Real.sq_sqrt hlambda.le
    have hthetaRoot := Real.sq_sqrt htheta
    have hnorm : 0 ≤ theta ⬝ᵥ theta := by
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (theta i))
    have hn := Real.sq_sqrt hnorm
    have hh : Real.sqrt lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) ≤
        Real.sqrt (theta ⬝ᵥ theta) := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      simpa only [mul_pow, hll, hthetaRoot, hn] using hqt
    have he : lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) / Real.sqrt lambda =
        Real.sqrt lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) := by
      apply (div_eq_iff (Real.sqrt_ne_zero'.mpr hlambda)).mpr
      calc
        lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) =
            (Real.sqrt lambda) ^ 2 * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) := by rw [hll]
        _ = _ := by ring
    rw [he]
    exact hh
  have hb : |lambda * (phi ⬝ᵥ (A *ᵥ theta))| ≤ Real.sqrt (theta ⬝ᵥ theta) * Real.sqrt v := by
    rw [abs_mul, abs_of_pos hlambda]
    calc
      lambda * |phi ⬝ᵥ (A *ᵥ theta)| ≤
          lambda * (Real.sqrt (phi ⬝ᵥ (A *ᵥ phi)) * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta))) :=
        mul_le_mul_of_nonneg_left
          (actual_positive_definite_bilinear_sqrt_bound A hi.1.inv phi theta) hlambda.le
      _ = (lambda * Real.sqrt (theta ⬝ᵥ (A *ᵥ theta)) / Real.sqrt lambda) * Real.sqrt v := by
        rw [hroot]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbiassqrt (Real.sqrt_nonneg _)
  have hn : |phi ⬝ᵥ (A *ᵥ (Phiᵀ *ᵥ noise))| ≤
      (Real.sqrt (actualFeatureNoiseQuadratic lambda Phi noise) / Real.sqrt lambda) * Real.sqrt v := by
    calc
      _ ≤ Real.sqrt (phi ⬝ᵥ (A *ᵥ phi)) * Real.sqrt (actualFeatureNoiseQuadratic lambda Phi noise) :=
        actual_positive_definite_bilinear_sqrt_bound A hi.1.inv phi (Phiᵀ *ᵥ noise)
      _ = _ := by rw [hroot]; ring
  rw [actual_feature_posterior_error_is_bias_minus_weighted_noise lambda hlambda Phi phi theta noise]
  calc
    _ ≤ |lambda * (phi ⬝ᵥ (A *ᵥ theta))| + |phi ⬝ᵥ (A *ᵥ (Phiᵀ *ᵥ noise))| := abs_sub _ _
    _ ≤ _ := by nlinarith [hb, hn]

end SafeLearning.CompleteModulesSafeOptPosteriorError
