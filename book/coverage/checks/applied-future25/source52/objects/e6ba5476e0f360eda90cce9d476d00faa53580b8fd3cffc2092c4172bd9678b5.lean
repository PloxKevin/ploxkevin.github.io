import SafeLearning.CompleteModulesSafeOptFiniteInformationBound
import SafeLearning.CompleteModulesSafeOptKernelPosteriorError

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesLandscapeZeroInformation

open CompleteFoundationsSequentialLogDet CompleteModulesSafeOptGPInformationBudget
open CompleteModulesSafeOptFiniteInformationBound CompleteModulesSafeOptPosteriorError
open CompleteModulesSafeOptKernelPosteriorError

/-- Positive regularization makes every PSD spectral determinant factor at
least one. Nonpositive normalized information therefore forces every
eigenvalue, and the actual matrix itself, to vanish. -/
theorem actual_nonpositive_normalized_psd_information_forces_the_matrix_to_vanish
    {index : Type*} [Fintype index] [DecidableEq index]
    (G : Matrix index index ℝ) (hG : G.PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hinformation : (1 / 2) * Real.log ((1 + lambda⁻¹ • G).det) ≤ 0) : G = 0 := by
  have hspectral :=
    actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
      G hG lambda⁻¹ (inv_nonneg.mpr hlambda.le)
  have hlog : Real.log ((1 + lambda⁻¹ • G).det) ≤ 0 := by linarith
  have hdet : (1 + lambda⁻¹ • G).det = 1 :=
    le_antisymm ((Real.log_nonpos_iff (zero_le_one.trans hspectral.2)).mp hlog) hspectral.2
  have hfactor : ∀ i, 1 ≤ 1 + lambda⁻¹ * hG.isHermitian.eigenvalues i :=
    fun i => le_add_of_nonneg_right
      (mul_nonneg (inv_nonneg.mpr hlambda.le) (hG.eigenvalues_nonneg i))
  have heigen : hG.isHermitian.eigenvalues = 0 := by
    ext i
    have hsingle : 1 + lambda⁻¹ * hG.isHermitian.eigenvalues i ≤
        ∏ j, (1 + lambda⁻¹ * hG.isHermitian.eigenvalues j) := by
      simpa only [Finset.prod_singleton] using
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ {i})
          (fun j _ => zero_le_one.trans (hfactor j)) (fun j _ _ => hfactor j)
    rw [← hspectral.1, hdet] at hsingle
    have hpositive : 0 < lambda⁻¹ := inv_pos.mpr hlambda
    have hnonnegative := hG.eigenvalues_nonneg i
    change hG.isHermitian.eigenvalues i = 0
    nlinarith
  exact hG.isHermitian.eigenvalues_eq_zero_iff.mp heigen

/-- The Gram matrix is computed from the actual feature entries. Zero
normalized information makes each squared entry vanish, including empty
sample or feature dimensions. -/
theorem actual_nonpositive_feature_information_forces_the_sampled_features_to_vanish
    {sample feature : Type*} [Fintype sample] [Fintype feature]
    [DecidableEq sample] [DecidableEq feature]
    (Phi : Matrix sample feature ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hinformation : (1 / 2) * Real.log ((1 + lambda⁻¹ • featureGram Phi).det) ≤ 0) :
    Phi = 0 := by
  have hG : (featureGram Phi).PosSemidef := by
    simpa only [featureGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Phi
  have hzero := actual_nonpositive_normalized_psd_information_forces_the_matrix_to_vanish
    (featureGram Phi) hG lambda hlambda hinformation
  ext i j
  have hdiagonal : (∑ k : sample, Phi k j * Phi k j) = 0 := by
    simpa only [featureGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using
      congrArg (fun M : Matrix feature feature ℝ => M j j) hzero
  have hsingle := Finset.single_le_sum (fun k _ => mul_self_nonneg (Phi k j))
    (Finset.mem_univ i)
  rw [hdiagonal] at hsingle
  change Phi i j = 0
  nlinarith [mul_self_nonneg (Phi i j)]

/-- Every noise vector is permitted. The actual feature noise vector and
both computed regularized feature/kernel noise quadratics are exactly zero. -/
theorem actual_nonpositive_feature_information_annihilates_every_noise_quadratic
    {sample feature : Type*} [Fintype sample] [Fintype feature]
    [DecidableEq sample] [DecidableEq feature]
    (Phi : Matrix sample feature ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hinformation : (1 / 2) * Real.log ((1 + lambda⁻¹ • featureGram Phi).det) ≤ 0)
    (noise : sample → ℝ) :
    Phiᵀ *ᵥ noise = 0 ∧ actualFeatureNoiseQuadratic lambda Phi noise = 0 ∧
      noise ⬝ᵥ (kernelGram Phi *ᵥ ((noisyKernel lambda Phi)⁻¹ *ᵥ noise)) = 0 := by
  have hPhi := actual_nonpositive_feature_information_forces_the_sampled_features_to_vanish
    Phi lambda hlambda hinformation
  simp [hPhi, actualFeatureNoiseQuadratic, kernelGram]

/-- The same statement uses the actual realized repeated-design kernel
information. Sylvester's identity transfers its determinant to the actual
feature Gram; no desired noise bound is supplied. -/
theorem actual_nonpositive_realized_kernel_information_forces_zero_sampled_features_and_noise
    {X feature : Type*} [Fintype feature] [DecidableEq feature]
    (kernel : X → X → ℝ) (features : X → feature → ℝ)
    (hfeatures : ∀ x y, kernel x y = features x ⬝ᵥ features y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (T : ℕ)
    (hinformation : actualKernelDesignInformation kernel lambda T (fun i => query i) ≤ 0)
    (noise : ℕ → ℝ) :
    (fun i : Fin T => features (query i)) = (0 : Matrix (Fin T) feature ℝ) ∧
      actualKernelPastGram kernel query T = 0 ∧
        actualKernelNoiseQuadratic kernel lambda query noise T = 0 := by
  let Phi : Matrix (Fin T) feature ℝ := fun i => features (query i)
  have hgram : kernelGram Phi = actualKernelPastGram kernel query T := by
    ext i j
    change features (query i) ⬝ᵥ features (query j) = kernel (query i) (query j)
    exact (hfeatures (query i) (query j)).symm
  have hdet : (1 + lambda⁻¹ • kernelGram Phi).det =
      (1 + lambda⁻¹ • featureGram Phi).det := by
    simpa only [featureGram, kernelGram, Matrix.mul_smul, Matrix.smul_mul] using
      CompleteFoundationsUniversalMatrices.actual_sylvester_determinant_identity
        (lambda⁻¹ • Phi) Phiᵀ
  have hinfo : (1 / 2) * Real.log ((1 + lambda⁻¹ • featureGram Phi).det) ≤ 0 := by
    rw [← hdet, hgram]
    exact hinformation
  have hPhi := actual_nonpositive_feature_information_forces_the_sampled_features_to_vanish
    Phi lambda hlambda hinfo
  have hkernel : actualKernelPastGram kernel query T = 0 := by
    rw [← hgram, hPhi]
    simp [kernelGram]
  refine ⟨hPhi, hkernel, ?_⟩
  simp [actualKernelNoiseQuadratic, hkernel]

/-- The genuine attained finite-design maximum bounds every actual repeated
design. If that maximum is nonpositive, every realized past Gram and noise
quadratic vanishes, without dividing by the information gain. -/
theorem actual_nonpositive_finite_maximum_information_forces_zero_realized_noise_quadratics
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (T : ℕ)
    (hmaximum : actualFiniteMaximumKernelInformationGain kernel lambda T ≤ 0) :
    ∀ (query : ℕ → X) (noise : ℕ → ℝ),
      actualKernelPastGram kernel query T = 0 ∧
        actualKernelNoiseQuadratic kernel lambda query noise T = 0 := by
  obtain ⟨features, hfeatures⟩ :=
    actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  intro query noise
  have hinfo : actualKernelDesignInformation kernel lambda T (fun i => query i) ≤ 0 :=
    ((actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design
      kernel lambda T).2 (Set.mem_range.mpr ⟨(fun i => query i), rfl⟩)).trans hmaximum
  exact (actual_nonpositive_realized_kernel_information_forces_zero_sampled_features_and_noise
    kernel features hfeatures lambda hlambda query T hinfo noise).2

end SafeLearning.CompleteModulesLandscapeZeroInformation
