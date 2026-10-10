import SafeLearning.CompleteModulesSafeOptGaussianGapPosterior

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology Matrix
namespace SafeLearning.CompleteModulesSafeOptGaussianGapDecay
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapGram
open CompleteModulesSafeOptGaussianGapPosterior CompleteModulesMatrixGP

theorem actual_unit_lengthscale_gaussian_correlation_with_a_fixed_input_tends_to_zero
    (input : ℝ) : Tendsto (actualGaussianKernel input) atTop (nhds 0) := by
  have hd : Tendsto (fun target : ℝ => target-input) atTop atTop :=
    tendsto_id.atTop_sub_const input
  have hs := (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp hd
  have ha : Tendsto (fun target : ℝ => (target-input)^2/2) atTop atTop :=
    hs.atTop_div_const (by norm_num)
  have hn := tendsto_neg_atTop_atBot.comp ha
  convert Real.tendsto_exp_atBot.comp hn using 1
  funext target
  unfold actualGaussianKernel
  congr 1
  ring

theorem actual_fixed_finite_gaussian_posterior_mean_returns_to_the_zero_prior_mean
    {n : ℕ} (input : Fin n → ℝ) (regularizer : ℝ) :
    Tendsto (actualGaussianMean input regularizer) atTop (nhds 0) := by
  let weights := (ridgeMatrix (actualGaussianGram input) regularizer)⁻¹ *ᵥ
    (fun i => actualGapFunction (input i))
  have h : Tendsto (fun target : ℝ => ∑ i, actualGaussianKernel (input i) target*weights i)
      atTop (nhds (∑ i, (0:ℝ)*weights i)) := by
    apply tendsto_finset_sum
    intro i hi
    exact (actual_unit_lengthscale_gaussian_correlation_with_a_fixed_input_tends_to_zero (input i)).mul
      tendsto_const_nhds
  simpa only [actualGaussianMean,CompleteModulesMatrixGP.posteriorMean,actualGaussianCross,
    dotProduct,weights,zero_mul,Finset.sum_const_zero] using h

theorem actual_fixed_finite_gaussian_posterior_variance_returns_to_the_unit_prior_variance
    {n : ℕ} (input : Fin n → ℝ) (regularizer : ℝ) :
    Tendsto (actualGaussianVariance input regularizer) atTop (nhds 1) := by
  let inverse := (ridgeMatrix (actualGaussianGram input) regularizer)⁻¹
  have hrow (i : Fin n) : Tendsto (fun target : ℝ =>
      (inverse *ᵥ actualGaussianCross input target) i) atTop (nhds 0) := by
    have h : Tendsto (fun target : ℝ => ∑ j, inverse i j*actualGaussianKernel (input j) target)
        atTop (nhds (∑ j, inverse i j*(0:ℝ))) := by
      apply tendsto_finset_sum
      intro j hj
      exact tendsto_const_nhds.mul
        (actual_unit_lengthscale_gaussian_correlation_with_a_fixed_input_tends_to_zero (input j))
    simpa only [Matrix.mulVec,dotProduct,actualGaussianCross,mul_zero,Finset.sum_const_zero] using h
  have hquad : Tendsto (fun target : ℝ => actualGaussianCross input target ⬝ᵥ
      (inverse *ᵥ actualGaussianCross input target)) atTop (nhds 0) := by
    have h : Tendsto (fun target : ℝ => ∑ i, actualGaussianKernel (input i) target*
        (inverse *ᵥ actualGaussianCross input target) i) atTop (nhds (∑ _i : Fin n, (0:ℝ)*(0:ℝ))) := by
      apply tendsto_finset_sum
      intro i hi
      exact (actual_unit_lengthscale_gaussian_correlation_with_a_fixed_input_tends_to_zero (input i)).mul
        (hrow i)
    simpa only [dotProduct,actualGaussianCross,mul_zero,Finset.sum_const_zero] using h
  simpa only [actualGaussianVariance,CompleteModulesMatrixGP.posteriorVariance,inverse,sub_zero] using
    tendsto_const_nhds.sub hquad

theorem actual_fixed_radius_gaussian_lower_bound_tends_to_the_prior_lower_bound
    {n : ℕ} (input : Fin n → ℝ) (regularizer radius : ℝ) :
    Tendsto (fun target => actualGaussianMean input regularizer target-
      radius*Real.sqrt (actualGaussianVariance input regularizer target)) atTop (nhds (-radius)) := by
  have hs := (Real.continuous_sqrt.tendsto (1:ℝ)).comp
    (actual_fixed_finite_gaussian_posterior_variance_returns_to_the_unit_prior_variance input regularizer)
  have hm := actual_fixed_finite_gaussian_posterior_mean_returns_to_the_zero_prior_mean input regularizer
  simpa only [Real.sqrt_one,mul_one,zero_sub] using hm.sub (tendsto_const_nhds.mul hs)

theorem actual_fixed_data_positive_radius_gaussian_lower_bound_eventually_fails_a_nonnegative_threshold
    {n : ℕ} (input : Fin n → ℝ) (regularizer radius threshold : ℝ)
    (hradius : 0 < radius) (hthreshold : 0 ≤ threshold) :
    ∀ᶠ target in atTop, actualGaussianMean input regularizer target-
      radius*Real.sqrt (actualGaussianVariance input regularizer target) < threshold := by
  have h := actual_fixed_radius_gaussian_lower_bound_tends_to_the_prior_lower_bound input regularizer radius
  have hz : ∀ᶠ target in atTop, actualGaussianMean input regularizer target-
      radius*Real.sqrt (actualGaussianVariance input regularizer target) < 0 :=
    (tendsto_order.mp h).2 0 (by linarith)
  exact hz.mono (fun _ ht => lt_of_lt_of_le ht hthreshold)

end SafeLearning.CompleteModulesSafeOptGaussianGapDecay
