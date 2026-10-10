import SafeLearning.CompleteModulesSafeOptGaussianGapDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology Matrix
namespace SafeLearning.CompleteModulesSafeOptGaussianGapDecayConsequences
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapFeatures
open CompleteModulesSafeOptGaussianGapPosterior CompleteModulesSafeOptGaussianGapDecay
open CompleteModulesMatrixGP

theorem actual_fixed_finite_gaussian_gp_mean_with_arbitrary_labels_returns_to_the_prior
    {n : ℕ} (input : Fin n → ℝ) (labels : Fin n → ℝ) (regularizer : ℝ) :
    Tendsto (fun target => posteriorMean (actualGaussianGram input)
      (actualGaussianCross input target) labels regularizer) atTop (nhds 0) := by
  let weights := (ridgeMatrix (actualGaussianGram input) regularizer)⁻¹ *ᵥ labels
  have h : Tendsto (fun target : ℝ => ∑ i, actualGaussianKernel (input i) target*weights i)
      atTop (nhds (∑ i, (0:ℝ)*weights i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (actual_unit_lengthscale_gaussian_correlation_with_a_fixed_input_tends_to_zero (input i)).mul
      tendsto_const_nhds
  simpa only [posteriorMean,actualGaussianCross,dotProduct,weights,zero_mul,Finset.sum_const_zero] using h

theorem actual_fixed_finite_gaussian_gp_lower_bound_eventually_fails_every_threshold_above_its_prior_lower
    {n : ℕ} (input : Fin n → ℝ) (labels : Fin n → ℝ) (regularizer radius threshold : ℝ)
    (hprior : -radius < threshold) :
    ∀ᶠ target in atTop, posteriorMean (actualGaussianGram input)
      (actualGaussianCross input target) labels regularizer-
      radius*Real.sqrt (actualGaussianVariance input regularizer target) < threshold := by
  have hs := (Real.continuous_sqrt.tendsto (1:ℝ)).comp
    (actual_fixed_finite_gaussian_posterior_variance_returns_to_the_unit_prior_variance input regularizer)
  have hm := actual_fixed_finite_gaussian_gp_mean_with_arbitrary_labels_returns_to_the_prior input labels regularizer
  have hlower : Tendsto (fun target => posteriorMean (actualGaussianGram input)
      (actualGaussianCross input target) labels regularizer-
      radius*Real.sqrt (actualGaussianVariance input regularizer target)) atTop (nhds (-radius)) := by
    simpa only [Function.comp_def,Real.sqrt_one,mul_one,zero_sub] using
      hm.sub (tendsto_const_nhds.mul hs)
  exact (tendsto_order.mp hlower).2 threshold hprior

theorem actual_every_gaussian_coefficient_evaluation_is_at_least_its_negative_rkhs_norm
    (coefficient : ActualCoefficientSpace) (point : ℝ) :
    -‖coefficient‖ ≤ inner ℝ coefficient (actualFeatureVector point) := by
  have h := abs_real_inner_le_norm coefficient (actualFeatureVector point)
  rw [actual_infinite_feature_vector_has_unit_norm,mul_one] at h
  exact (abs_le.mp h).1

theorem actual_unsafe_point_with_a_valid_gaussian_rkhs_radius_forces_prior_lower_below_the_threshold
    (coefficient : ActualCoefficientSpace) (radius threshold unsafePoint : ℝ)
    (hvalid : ‖coefficient‖ ≤ radius)
    (hunsafe : inner ℝ coefficient (actualFeatureVector unsafePoint) < threshold) :
    -radius < threshold := by
  have h := actual_every_gaussian_coefficient_evaluation_is_at_least_its_negative_rkhs_norm
    coefficient unsafePoint
  linarith

theorem actual_fixed_noise_free_gaussian_data_cannot_certify_sufficiently_distant_points_across_an_unsafe_hole
    {n : ℕ} (input : Fin n → ℝ) (coefficient : ActualCoefficientSpace)
    (regularizer radius threshold unsafePoint : ℝ) (hvalid : ‖coefficient‖ ≤ radius)
    (hunsafe : inner ℝ coefficient (actualFeatureVector unsafePoint) < threshold) :
    ∀ᶠ target in atTop, posteriorMean (actualGaussianGram input) (actualGaussianCross input target)
      (fun i => inner ℝ coefficient (actualFeatureVector (input i))) regularizer-
      radius*Real.sqrt (actualGaussianVariance input regularizer target) < threshold := by
  apply actual_fixed_finite_gaussian_gp_lower_bound_eventually_fails_every_threshold_above_its_prior_lower
  exact actual_unsafe_point_with_a_valid_gaussian_rkhs_radius_forces_prior_lower_below_the_threshold
    coefficient radius threshold unsafePoint hvalid hunsafe

end SafeLearning.CompleteModulesSafeOptGaussianGapDecayConsequences
