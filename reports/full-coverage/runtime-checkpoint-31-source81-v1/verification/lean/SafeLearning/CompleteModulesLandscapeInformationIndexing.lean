import SafeLearning.CompleteModulesSafeOptGPInformationBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesLandscapeInformationIndexing

open CompleteFoundationsTemporalLogDet CompleteModulesSafeOptGPInformationBudget

private theorem actual_finite_psd_kernel_sequential_variance_is_nonnegative
    {X : Type*} [Fintype X] [DecidableEq X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (n : ℕ) :
    0 ≤ actualKernelSequentialVariance kernel lambda query n := by
  obtain ⟨features, hfeatures⟩ :=
    actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  rw [actual_real_features_give_the_actual_queried_kernel_posterior_variance
    kernel features hfeatures lambda query n]
  exact (actual_regularized_finite_feature_posterior_variance_lies_between_zero_and_the_prior
    lambda hlambda (temporalFeatures (fun i => features (query i)) n) (features (query n))).1

/-- Every actual repeated finite design has nonnegative information,
including the empty design. No unit prior-variance bound is used. -/
theorem actual_finite_psd_kernel_every_repeated_design_information_is_nonnegative
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (n : ℕ) (design : Fin n → X) :
    0 ≤ actualKernelDesignInformation kernel lambda n design := by
  classical
  let query : ℕ → X := fun i => if hi : i < n then design ⟨i, hi⟩ else Classical.choice inferInstance
  have heq : (fun i : Fin n => query i) = design := by
    funext i
    simp only [query, dif_pos i.isLt]
  have hidentity := actual_finite_kernel_sequential_log_factors_equal_the_realized_design_logdet
    kernel hkernel lambda hlambda query n
  rw [heq] at hidentity
  have hsum : 0 ≤ ∑ i ∈ Finset.range n,
      Real.log (1 + actualKernelSequentialVariance kernel lambda query i / lambda) := by
    apply Finset.sum_nonneg
    intro i _
    exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg
      (actual_finite_psd_kernel_sequential_variance_is_nonnegative kernel hkernel lambda hlambda query i)
      hlambda.le))
  rw [hidentity] at hsum
  linarith

/-- Adding the actual next observation increases realized information by
one nonnegative posterior log factor. The genuine next-length design
maximum therefore bounds the current n-observation information. -/
theorem actual_finite_psd_kernel_realized_information_is_bounded_by_the_next_round_maximum
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (n : ℕ) :
    actualKernelDesignInformation kernel lambda n (fun i => query i) ≤
      actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) := by
  have hprevious := actual_finite_kernel_sequential_log_factors_equal_the_realized_design_logdet
    kernel hkernel lambda hlambda query n
  have hnext := actual_finite_kernel_sequential_log_factors_equal_the_realized_design_logdet
    kernel hkernel lambda hlambda query (n + 1)
  rw [Finset.sum_range_succ, hprevious] at hnext
  have hlog : 0 ≤ Real.log (1 + actualKernelSequentialVariance kernel lambda query n / lambda) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg
      (actual_finite_psd_kernel_sequential_variance_is_nonnegative kernel hkernel lambda hlambda query n)
      hlambda.le))
  have hstep : actualKernelDesignInformation kernel lambda n (fun i => query i) ≤
      actualKernelDesignInformation kernel lambda (n + 1) (fun i => query i) := by linarith
  exact hstep.trans
    ((actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design
      kernel lambda (n + 1)).2 (Set.mem_range.mpr ⟨(fun i => query i), rfl⟩))

end SafeLearning.CompleteModulesLandscapeInformationIndexing
