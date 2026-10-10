import SafeLearning.CompleteModulesSafeOptGaussianGapSeries
import SafeLearning.CompleteModulesGramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptGaussianGapFeatures
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesKernel CompleteModulesGramBridge

abbrev ActualCoefficientSpace := lp (fun _ : ℕ => ℝ) 2

def actualFeatureVector (x : ℝ) : ActualCoefficientSpace :=
  ⟨(fun n => actualGaussianFeature n x),memℓp_gen (by
    simpa [Real.norm_eq_abs,Real.rpow_two,sq_abs] using
      (actual_gaussian_feature_vector_has_unit_sum_of_squares x).summable)⟩

theorem actual_feature_vector_coordinates (x : ℝ) (n : ℕ) :
    actualFeatureVector x n=actualGaussianFeature n x := rfl

theorem actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel
    (x y : ℝ) : inner ℝ (actualFeatureVector x) (actualFeatureVector y)=actualGaussianKernel x y := by
  have h := lp.hasSum_inner (𝕜:=ℝ) (actualFeatureVector x) (actualFeatureVector y)
  have hreal : HasSum (fun n => actualGaussianFeature n x*actualGaussianFeature n y)
      (inner ℝ (actualFeatureVector x) (actualFeatureVector y)) := by
    simpa [RCLike.inner_apply,conj_trivial,mul_comm,actual_feature_vector_coordinates] using h
  exact hreal.unique (actual_squared_exponential_kernel_has_the_literal_infinite_feature_expansion x y)

theorem actual_infinite_feature_vector_has_unit_norm (x : ℝ) : ‖actualFeatureVector x‖=1 := by
  have h := actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel x x
  rw [real_inner_self_eq_norm_sq] at h
  simp only [actualGaussianKernel,sub_self,zero_pow (by decide : (2:ℕ)≠0),neg_zero,
    zero_div,Real.exp_zero] at h
  nlinarith [norm_nonneg (actualFeatureVector x)]

theorem actual_gaussian_kernel_gram_on_every_finite_real_dataset_is_positive_semidefinite
    {I : Type*} [Fintype I] (input : I → ℝ) :
    (Matrix.of (fun i j => actualGaussianKernel (input i) (input j))).PosSemidef := by
  have he : Matrix.of (fun i j => actualGaussianKernel (input i) (input j))=
      Matrix.gram ℝ (fun i => actualFeatureVector (input i)) := by
    ext i j
    simp [Matrix.gram_apply,actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel]
  rw [he]
  exact Matrix.posSemidef_gram ℝ (fun i => actualFeatureVector (input i))

def actualSourceCoefficient : ActualCoefficientSpace :=
  Real.sqrt 2 • lp.single 2 2 (1:ℝ)-(1/5:ℝ) • lp.single 2 1 (1:ℝ)+
    (3/400:ℝ) • lp.single 2 0 (1:ℝ)

theorem actual_source_coefficient_evaluates_to_the_printed_gap_function (x : ℝ) :
    inner ℝ actualSourceCoefficient (actualFeatureVector x)=actualGapFunction x := by
  rw [actual_source_gap_function_is_exactly_the_printed_three_feature_combination]
  simp [actualSourceCoefficient,inner_add_left,inner_sub_left,real_inner_smul_left,
    lp.inner_single_left,actual_feature_vector_coordinates,RCLike.inner_apply,conj_trivial]

theorem actual_source_coefficient_has_exact_squared_hilbert_norm :
    ‖actualSourceCoefficient‖^2=(326409/160000:ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [actualSourceCoefficient,inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,lp.inner_single_left,lp.coeFn_single,
    RCLike.inner_apply,conj_trivial]
  norm_num [Real.sq_sqrt]

theorem actual_every_coefficient_function_obeys_the_true_regularized_noise_free_posterior_bound
    {I : Type*} [Fintype I] [DecidableEq I] (input : I → ℝ) (target : ℝ)
    (coefficient : ActualCoefficientSpace) (regularizer : ℝ) (hreg : 0<regularizer) :
    let feature := fun i => actualFeatureVector (input i)
    let weights := ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ
      (fun i => actualGaussianKernel (input i) target))
    |inner ℝ coefficient (actualFeatureVector target)-
      ∑ i, weights i*inner ℝ coefficient (feature i)|≤
      ‖coefficient‖*Real.sqrt (posteriorVariance feature (actualFeatureVector target) weights) := by
  let feature := fun i => actualFeatureVector (input i)
  let weights := ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ
    (fun i => actualGaussianKernel (input i) target))
  have hs := inverse_weights_solve_normal_system feature regularizer
    (positive_regularization_determinant_nonzero feature regularizer hreg)
    (fun i => actualGaussianKernel (input i) target)
  have hnormal : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weights j)+
      regularizer*weights i=inner ℝ (feature i) (actualFeatureVector target) := by
    intro i
    rw [actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel]
    exact hs i
  exact noiseless_posterior_error feature (actualFeatureVector target) coefficient weights
    regularizer ‖coefficient‖ hreg.le le_rfl hnormal

end SafeLearning.CompleteModulesSafeOptGaussianGapFeatures
