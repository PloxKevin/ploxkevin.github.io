import SafeLearning.CompleteModulesSafeOptGaussianGapFeatures

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesSafeOptGaussianGapGram
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapFeatures
open CompleteModulesKernel CompleteModulesGramBridge

theorem actual_gaussian_features_at_any_finite_distinct_inputs_are_linearly_independent
    {n : ℕ} (input : Fin n → ℝ) (hinjective : Function.Injective input) :
    LinearIndependent ℝ (fun i => actualFeatureVector (input i)) := by
  rw [Fintype.linearIndependent_iff]
  intro weights hsum
  let scaled : Fin n → ℝ := fun i => weights i*Real.exp (-((input i)^2)/2)
  have hmoments (k : Fin n) : ∑ i, scaled i*(input i)^k.val=0 := by
    have h := congrArg (fun v : ActualCoefficientSpace => v k.val) hsum
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      actual_feature_vector_coordinates,lp.coeFn_zero,Pi.zero_apply] at h
    have hf : (0:ℝ)<k.val.factorial := by exact_mod_cast k.val.factorial_pos
    have hsqrt : Real.sqrt (k.val.factorial:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.2 hf)
    calc
      ∑ i, scaled i*(input i)^k.val =
          Real.sqrt (k.val.factorial:ℝ)*∑ i, weights i*actualGaussianFeature k.val (input i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [scaled,actualGaussianFeature]
        field_simp
      _ = 0 := by rw [h,mul_zero]
  have hs : scaled=0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinjective hmoments
  intro i
  have hi := congrFun hs i
  change weights i*Real.exp (-((input i)^2)/2)=0 at hi
  exact (mul_eq_zero.mp hi).resolve_right (ne_of_gt (Real.exp_pos _))

theorem actual_gaussian_kernel_matrix_at_any_finite_distinct_inputs_is_positive_definite
    {n : ℕ} (input : Fin n → ℝ) (hinjective : Function.Injective input) :
    (featureGram (fun i => actualFeatureVector (input i))).PosDef := by
  rw [feature_gram_positive_definite_iff_independent]
  exact actual_gaussian_features_at_any_finite_distinct_inputs_are_linearly_independent input hinjective

def actualSourceInput (i : Fin 11) : ℝ := -1+(i.val:ℝ)/10

theorem actual_source_eleven_noise_free_inputs_are_distinct_and_have_a_positive_definite_gaussian_gram :
    Function.Injective actualSourceInput ∧
      (featureGram (fun i => actualFeatureVector (actualSourceInput i))).PosDef := by
  have hi : Function.Injective actualSourceInput := by
    intro i j he
    have hv : (i.val:ℝ)=(j.val:ℝ) := by dsimp [actualSourceInput] at he;linarith
    exact Fin.ext (Nat.cast_inj.mp hv)
  exact ⟨hi,actual_gaussian_kernel_matrix_at_any_finite_distinct_inputs_is_positive_definite actualSourceInput hi⟩

theorem actual_noise_free_bound_with_distinct_gaussian_inputs_allows_every_nonnegative_regularizer
    {n : ℕ} (input : Fin n → ℝ) (hinjective : Function.Injective input)
    (target : ℝ) (coefficient : ActualCoefficientSpace) (regularizer : ℝ) (hreg : 0≤regularizer) :
    let feature := fun i => actualFeatureVector (input i)
    let weights := ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ
      (fun i => actualGaussianKernel (input i) target))
    |inner ℝ coefficient (actualFeatureVector target)-∑ i, weights i*inner ℝ coefficient (feature i)|≤
      ‖coefficient‖*Real.sqrt (posteriorVariance feature (actualFeatureVector target) weights) := by
  let feature := fun i => actualFeatureVector (input i)
  let weights := ((CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer)⁻¹ *ᵥ
    (fun i => actualGaussianKernel (input i) target))
  have hg := actual_gaussian_kernel_matrix_at_any_finite_distinct_inputs_is_positive_definite input hinjective
  have hpd : (CompleteModulesMatrixGP.ridgeMatrix (featureGram feature) regularizer).PosDef := by
    exact hg.add_posSemidef (Matrix.PosSemidef.one.smul hreg)
  have hs := inverse_weights_solve_normal_system feature regularizer hpd.det_pos.ne'
    (fun i => actualGaussianKernel (input i) target)
  have hn : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weights j)+regularizer*weights i=
      inner ℝ (feature i) (actualFeatureVector target) := by
    intro i
    rw [actual_infinite_hilbert_feature_inner_product_is_the_literal_gaussian_kernel]
    exact hs i
  exact noiseless_posterior_error feature (actualFeatureVector target) coefficient weights
    regularizer ‖coefficient‖ hreg le_rfl hn

end SafeLearning.CompleteModulesSafeOptGaussianGapGram
