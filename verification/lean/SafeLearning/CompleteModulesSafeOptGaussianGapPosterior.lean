import SafeLearning.CompleteModulesSafeOptGaussianGapGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptGaussianGapPosterior
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapFeatures
open CompleteModulesSafeOptGaussianGapGram CompleteModulesKernel CompleteModulesGramBridge

def actualGaussianGram {n : ℕ} (input : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => actualGaussianKernel (input i) (input j))
def actualGaussianCross {n : ℕ} (input : Fin n → ℝ) (target : ℝ) : Fin n → ℝ :=
  fun i => actualGaussianKernel (input i) target
def actualGaussianMean {n : ℕ} (input : Fin n → ℝ) (regularizer target : ℝ) : ℝ :=
  CompleteModulesMatrixGP.posteriorMean (actualGaussianGram input) (actualGaussianCross input target)
    (fun i => actualGapFunction (input i)) regularizer
def actualGaussianVariance {n : ℕ} (input : Fin n → ℝ) (regularizer target : ℝ) : ℝ :=
  CompleteModulesMatrixGP.posteriorVariance (actualGaussianGram input)
    (actualGaussianCross input target) 1 regularizer

theorem actual_literal_gaussian_kernel_gram_is_exactly_the_derived_hilbert_feature_gram
    {n : ℕ} (input : Fin n → ℝ) :
    actualGaussianGram input=featureGram (fun i => actualFeatureVector (input i)) := by
  ext i j
  simp [actualGaussianGram,featureGram,Matrix.gram_apply,
    actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel]

theorem actual_literal_gp_mean_equals_the_true_source_coefficient_weighted_prediction
    {n : ℕ} (input : Fin n → ℝ) (hinjective : Function.Injective input)
    (regularizer target : ℝ) (hreg : 0≤regularizer) :
    let weights := ((CompleteModulesMatrixGP.ridgeMatrix (actualGaussianGram input) regularizer)⁻¹ *ᵥ
      actualGaussianCross input target)
    actualGaussianMean input regularizer target=∑ i, weights i*actualGapFunction (input i) := by
  let A := CompleteModulesMatrixGP.ridgeMatrix (actualGaussianGram input) regularizer
  have hpd : A.PosDef := by
    rw [show A=CompleteModulesMatrixGP.ridgeMatrix (actualGaussianGram input) regularizer by rfl,
      actual_literal_gaussian_kernel_gram_is_exactly_the_derived_hilbert_feature_gram]
    exact (actual_gaussian_kernel_matrix_at_any_finite_distinct_inputs_is_positive_definite input hinjective).add_posSemidef
      (Matrix.PosSemidef.one.smul hreg)
  have hs : A⁻¹.IsSymm := hpd.isHermitian.isSymm.inv
  have h := Matrix.dotProduct_transpose_mulVec A⁻¹
    (fun i => actualGapFunction (input i)) (actualGaussianCross input target)
  rw [hs] at h
  change actualGaussianCross input target ⬝ᵥ (A⁻¹ *ᵥ (fun i => actualGapFunction (input i)))=
    ∑ i, (A⁻¹ *ᵥ actualGaussianCross input target) i*actualGapFunction (input i)
  rw [← h]
  simp only [dotProduct,mul_comm]

theorem actual_literal_gp_variance_equals_the_derived_hilbert_posterior_variance
    {n : ℕ} (input : Fin n → ℝ) (regularizer target : ℝ) :
    let feature := fun i => actualFeatureVector (input i)
    let weights := ((CompleteModulesMatrixGP.ridgeMatrix (actualGaussianGram input) regularizer)⁻¹ *ᵥ
      actualGaussianCross input target)
    actualGaussianVariance input regularizer target=
      CompleteModulesKernel.posteriorVariance feature (actualFeatureVector target) weights := by
  simp only [actualGaussianVariance,CompleteModulesMatrixGP.posteriorVariance,
    CompleteModulesKernel.posteriorVariance,actual_infinite_feature_vector_has_unit_norm,one_pow,
    actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel,
    actualGaussianCross,dotProduct,mul_comm]

theorem actual_source_function_obeys_the_literal_matrix_gp_noise_free_confidence_bound
    {n : ℕ} (input : Fin n → ℝ) (hinjective : Function.Injective input)
    (regularizer target : ℝ) (hreg : 0≤regularizer) :
    |actualGapFunction target-actualGaussianMean input regularizer target|≤
      Real.sqrt (326409/160000:ℝ)*Real.sqrt (actualGaussianVariance input regularizer target) := by
  have h := actual_noise_free_bound_with_distinct_gaussian_inputs_allows_every_nonnegative_regularizer
    input hinjective target actualSourceCoefficient regularizer hreg
  dsimp only at h
  simp_rw [actual_source_coefficient_evaluates_to_the_printed_gap_function] at h
  have hn : ‖actualSourceCoefficient‖=Real.sqrt (326409/160000:ℝ) := by
    rw [← actual_source_coefficient_has_exact_squared_hilbert_norm,Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at h
  rw [actual_literal_gp_mean_equals_the_true_source_coefficient_weighted_prediction input hinjective regularizer target hreg,
    actual_literal_gp_variance_equals_the_derived_hilbert_posterior_variance]
  rw [actual_literal_gaussian_kernel_gram_is_exactly_the_derived_hilbert_feature_gram]
  exact h

theorem actual_source_eleven_point_regularized_lower_bound_is_a_genuine_safe_certificate
    (target : ℝ) (hcertificate : (0:ℝ)≤actualGaussianMean actualSourceInput (1/10000000000) target-
      Real.sqrt (326409/160000:ℝ)*Real.sqrt
        (actualGaussianVariance actualSourceInput (1/10000000000) target)) :
    0≤actualGapFunction target := by
  have h := actual_source_function_obeys_the_literal_matrix_gp_noise_free_confidence_bound
    actualSourceInput actual_source_eleven_noise_free_inputs_are_distinct_and_have_a_positive_definite_gaussian_gram.1
    (1/10000000000) target (by norm_num)
  have hl := (abs_le.mp h).1
  linarith

end SafeLearning.CompleteModulesSafeOptGaussianGapPosterior
