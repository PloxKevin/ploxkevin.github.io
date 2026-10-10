import SafeLearning.CompleteFoundationsTelescopingApplications

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix MatrixOrder

namespace SafeLearning.CompleteModulesSafeOptGPInformationBudget

open SafeLearning.CompleteFoundationsSequentialLogDet
open SafeLearning.CompleteFoundationsTemporalLogDet
open SafeLearning.CompleteFoundationsTelescopingApplications

variable {X : Type*}

def actualKernelPastGram (kernel : X → X → ℝ) (query : ℕ → X) (t : ℕ) :
    Matrix (Fin t) (Fin t) ℝ := fun i j => kernel (query i) (query j)

def actualKernelPastCross (kernel : X → X → ℝ) (query : ℕ → X) (t : ℕ) : Fin t → ℝ :=
  fun i => kernel (query i) (query t)

/-- The actual latent posterior variance before the current query, with the
positive regularizer added to the past Gram matrix. Repeated queries remain. -/
def actualKernelSequentialVariance (kernel : X → X → ℝ) (lambda : ℝ)
    (query : ℕ → X) (t : ℕ) : ℝ :=
  kernel (query t) (query t) - actualKernelPastCross kernel query t ⬝ᵥ
    ((lambda • 1 + actualKernelPastGram kernel query t)⁻¹ *ᵥ actualKernelPastCross kernel query t)

def actualKernelDesignInformation (kernel : X → X → ℝ) (lambda : ℝ) (T : ℕ)
    (design : Fin T → X) : ℝ :=
  (1 / 2) * Real.log ((1 + lambda⁻¹ • (fun i j => kernel (design i) (design j))).det)

/-- The maximum is over every repeated finite query design in the actual
finite domain. It is constructed as the real supremum of that finite image. -/
def actualFiniteMaximumKernelInformationGain (kernel : X → X → ℝ) (lambda : ℝ) (T : ℕ) : ℝ :=
  sSup (range (actualKernelDesignInformation kernel lambda T))

/-- Every finite real PSD kernel has an actual finite real feature map.
The representation is derived from the matrix square root. -/
theorem actual_finite_positive_semidefinite_kernel_has_real_features
    [Fintype X] [DecidableEq X] (kernel : X → X → ℝ)
    (hkernel : (kernel : Matrix X X ℝ).PosSemidef) :
    ∃ features : X → X → ℝ, ∀ x y, kernel x y = features x ⬝ᵥ features y := by
  let A := CFC.sqrt (kernel : Matrix X X ℝ)
  have htranspose : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (kernel : Matrix X X ℝ)).posSemidef.isHermitian
  have hproduct : A * Aᵀ = kernel := by
    rw [htranspose]
    simpa only [pow_two] using CFC.sq_sqrt (kernel : Matrix X X ℝ) hkernel.nonneg
  refine ⟨A,?_⟩
  intro x y
  have h := congrArg (fun M : Matrix X X ℝ => M x y) hproduct
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,dotProduct] using h.symm

/-- Positive regularization derives nonnegative latent variance. Subtracting
the inverse-kernel nonnegative quadratic also bounds it by the actual prior. -/
theorem actual_regularized_finite_feature_posterior_variance_lies_between_zero_and_the_prior
    {sample feature : Type*} [Fintype sample] [Fintype feature]
    [DecidableEq sample] [DecidableEq feature]
    (lambda : ℝ) (hlambda : 0 < lambda) (Phi : Matrix sample feature ℝ) (phi : feature → ℝ) :
    posteriorVariance lambda Phi phi ∈ Icc 0 (phi ⬝ᵥ phi) := by
  have hregularized := actual_regularized_feature_and_kernel_invertible lambda hlambda Phi
  have hfeature := hregularized.1.inv.posSemidef.dotProduct_mulVec_nonneg phi
  have hscaled : 0 ≤ posteriorVariance lambda Phi phi / lambda := by
    rw [← actual_posterior_variance_equals_feature_inverse lambda hlambda Phi phi]
    simpa only [star_trivial] using hfeature
  have hkernel := hregularized.2.2.1.inv.posSemidef.dotProduct_mulVec_nonneg (Phi *ᵥ phi)
  have hquadratic : 0 ≤ (Phi *ᵥ phi) ⬝ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ (Phi *ᵥ phi)) := by
    simpa only [star_trivial] using hkernel
  refine ⟨(div_nonneg_iff_of_pos hlambda).mp hscaled,?_⟩
  dsimp only [posteriorVariance]
  linarith

/-- The derived feature variance is exactly the standard queried-kernel
posterior formula, rather than a separate variance supplied as a hypothesis. -/
theorem actual_real_features_give_the_actual_queried_kernel_posterior_variance
    {feature : Type*} [Fintype feature] [DecidableEq feature]
    (kernel : X → X → ℝ) (features : X → feature → ℝ)
    (hfeatures : ∀ x y, kernel x y = features x ⬝ᵥ features y)
    (lambda : ℝ) (query : ℕ → X) (t : ℕ) :
    actualKernelSequentialVariance kernel lambda query t =
      temporalVariance lambda (fun j => features (query j)) t := by
  have hgram : kernelGram (temporalFeatures (fun j => features (query j)) t) =
      actualKernelPastGram kernel query t := by
    ext i j
    simpa only [kernelGram,temporalFeatures,Matrix.mul_apply,Matrix.transpose_apply,
      actualKernelPastGram,dotProduct] using (hfeatures (query i) (query j)).symm
  have hcross : temporalFeatures (fun j => features (query j)) t *ᵥ features (query t) =
      actualKernelPastCross kernel query t := by
    ext i
    simpa only [temporalFeatures,Matrix.mulVec,actualKernelPastCross,dotProduct] using
      (hfeatures (query i) (query t)).symm
  dsimp only [actualKernelSequentialVariance,temporalVariance,posteriorVariance,noisyKernel]
  rw [hgram,hcross,← hfeatures (query t) (query t)]

/-- The real information supremum is attained over all repeated finite
designs, and every actual design is bounded by that genuine maximum. -/
theorem actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design
    [Fintype X] [Nonempty X] (kernel : X → X → ℝ) (lambda : ℝ) (T : ℕ) :
    IsGreatest (range (actualKernelDesignInformation kernel lambda T))
      (actualFiniteMaximumKernelInformationGain kernel lambda T) := by
  exact (range_nonempty _).isGreatest_csSup (finite_range _)

/-- An arbitrary normalized PSD kernel on a finite domain has actual queried
posterior variance in [0,1], including arbitrary repeated query sequences. -/
theorem actual_normalized_finite_kernel_sequential_posterior_variance_is_in_the_unit_interval
    [Fintype X] [DecidableEq X] (kernel : X → X → ℝ)
    (hkernel : (kernel : Matrix X X ℝ).PosSemidef) (hnormalized : ∀ x, kernel x x ≤ 1)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (t : ℕ) :
    actualKernelSequentialVariance kernel lambda query t ∈ Icc 0 1 := by
  obtain ⟨features,hfeatures⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  rw [actual_real_features_give_the_actual_queried_kernel_posterior_variance
    kernel features hfeatures lambda query t]
  have hvariance := actual_regularized_finite_feature_posterior_variance_lies_between_zero_and_the_prior
    lambda hlambda (temporalFeatures (fun j => features (query j)) t) (features (query t))
  refine ⟨hvariance.1,hvariance.2.trans ?_⟩
  rw [← hfeatures (query t) (query t)]
  exact hnormalized _

/-- The exact sequential logdet identity holds for any finite real PSD
kernel; the finite feature representation is derived internally. -/
theorem actual_finite_kernel_sequential_log_factors_equal_the_realized_design_logdet
    [Fintype X] [DecidableEq X] (kernel : X → X → ℝ)
    (hkernel : (kernel : Matrix X X ℝ).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (T : ℕ) :
    (∑ j ∈ Finset.range T, Real.log (1 + actualKernelSequentialVariance kernel lambda query j / lambda)) =
      2 * actualKernelDesignInformation kernel lambda T (fun i => query i) := by
  obtain ⟨features,hfeatures⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  have hgram : kernelGram (temporalFeatures (fun j => features (query j)) T) =
      (fun i j : Fin T => kernel (query i) (query j)) := by
    ext i j
    simpa only [kernelGram,temporalFeatures,Matrix.mul_apply,Matrix.transpose_apply,dotProduct] using
      (hfeatures (query i) (query j)).symm
  have h := actual_kernel_log_determinant_is_the_sum_of_sequential_log_factors
    lambda hlambda (fun j => features (query j)) T
  rw [hgram] at h
  simp_rw [← actual_real_features_give_the_actual_queried_kernel_posterior_variance
    kernel features hfeatures lambda query] at h
  dsimp only [actualKernelDesignInformation]
  linarith

/-- The true GP standard deviations and the actual maximum information gain
satisfy the precise primitive variance/information budget used by the finite
SafeOpt proof. Neither primitive bound is assumed as the desired conclusion. -/
theorem actual_normalized_finite_kernel_standard_deviations_satisfy_the_actual_maximum_information_budget
    [Fintype X] [DecidableEq X] [Nonempty X] (kernel : X → X → ℝ)
    (hkernel : (kernel : Matrix X X ℝ).PosSemidef) (hnormalized : ∀ x, kernel x x ≤ 1)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (T : ℕ) :
    (∀ j, (Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) ^ 2 ∈ Icc 0 1) ∧
    (∑ j ∈ Finset.range T, Real.log
      (1 + (Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) ^ 2 / lambda)) ≤
        2 * actualFiniteMaximumKernelInformationGain kernel lambda T := by
  have hvariance := actual_normalized_finite_kernel_sequential_posterior_variance_is_in_the_unit_interval
    kernel hkernel hnormalized lambda hlambda query
  have hsquare : ∀ j, (Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) ^ 2 =
      actualKernelSequentialVariance kernel lambda query j := fun j => Real.sq_sqrt (hvariance j).1
  refine ⟨fun j => hsquare j ▸ hvariance j,?_⟩
  simp_rw [hsquare]
  rw [actual_finite_kernel_sequential_log_factors_equal_the_realized_design_logdet
    kernel hkernel lambda hlambda query T]
  exact mul_le_mul_of_nonneg_left
    ((actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design
      kernel lambda T).2 (mem_range.mpr ⟨(fun i => query i),rfl⟩)) (by norm_num)

end SafeLearning.CompleteModulesSafeOptGPInformationBudget
