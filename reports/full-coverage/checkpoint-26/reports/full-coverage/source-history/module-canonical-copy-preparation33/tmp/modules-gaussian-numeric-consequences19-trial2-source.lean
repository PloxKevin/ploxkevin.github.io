import SafeLearning.CompleteModulesGaussianNumericData
import SafeLearning.CompleteModulesRidgeResidualBounds
import SafeLearning.CompleteModulesFiniteSumPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesGaussianNumericConsequences
open CompleteModulesGaussianNumericData CompleteModulesRidgeResidualBounds
open CompleteModulesFiniteSumPerturbation CompleteModulesMatrixGP
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapGram
open CompleteModulesSafeOptGaussianGapPosterior

def actualSourceWeight : Fin 11 → ℝ :=
  (ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000))⁻¹ *ᵥ
    actualGaussianCross actualSourceInput (1/5)

theorem actual_approximate_weights_have_small_residuals_in_the_literal_gaussian_system
    (i : Fin 11) :
    |actualGaussianCross actualSourceInput (1/5) i-
      (ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i| ≤
      1/10000000000000000000000000000 := by
  have hc := actual_source_gram_and_cross_entries_have_rigorous_table_error_bounds.2 i
  have ht := actual_rational_approximate_weights_have_small_true_table_system_residuals.1 i
  have hw := actual_rational_approximate_weights_have_small_true_table_system_residuals.2
  have hg := actual_weighted_finite_sum_error_is_bounded_by_component_error_and_total_weight
    (fun j => actualGramApproximation i j) (fun j => actualGaussianGram actualSourceInput i j)
    actualWeightApproximation (1/10000000000000000000000000000000)
    (fun j => by
      rw [abs_sub_comm]
      exact actual_source_gram_and_cross_entries_have_rigorous_table_error_bounds.1 i j)
  have heq :
      (ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i-
        (ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i=
      (∑ j, actualGramApproximation i j*actualWeightApproximation j)-
        (∑ j, actualGaussianGram actualSourceInput i j*actualWeightApproximation j) := by
    simp only [ridgeMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    simp only [Matrix.mulVec,dotProduct]
    ring
  have hridge :
      |(ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i-
        (ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i| ≤
      (1/10000000000000000000000000000000)*(∑ j, |actualWeightApproximation j|) := by
    rw [heq]
    exact hg
  calc
    _ ≤ |actualGaussianCross actualSourceInput (1/5) i-actualCrossApproximation i|+
        |actualCrossApproximation i-
          (ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i|+
        |(ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i-
          (ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i| := by
      have h1 := abs_sub_le (actualGaussianCross actualSourceInput (1/5) i) (actualCrossApproximation i)
        ((ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i)
      have h2 := abs_sub_le (actualCrossApproximation i)
        ((ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i)
        ((ridgeMatrix (actualGaussianGram actualSourceInput) (1/10000000000) *ᵥ actualWeightApproximation) i)
      linarith
    _ ≤ _ := by linarith

theorem actual_inverse_matrix_weights_are_rigorously_close_to_the_rational_candidates
    (i : Fin 11) : |actualSourceWeight i-actualWeightApproximation i| ≤
      4/1000000000000000000 := by
  have hgram : (actualGaussianGram actualSourceInput).PosSemidef := by
    rw [actual_literal_gaussian_kernel_gram_is_exactly_the_derived_hilbert_feature_gram]
    exact actual_source_eleven_noise_free_inputs_are_distinct_and_have_a_positive_definite_gaussian_gram.2.posSemidef
  have h := actual_eleven_dimensional_ridge_inverse_error_bound_from_component_residuals
    (actualGaussianGram actualSourceInput) hgram (1/10000000000)
    (1/10000000000000000000000000000) (by norm_num) (by norm_num)
    (actualGaussianCross actualSourceInput (1/5)) actualWeightApproximation
    actual_approximate_weights_have_small_residuals_in_the_literal_gaussian_system i
  norm_num [actualSourceWeight] at h ⊢
  exact h

theorem actual_source_labels_and_cross_entries_have_small_absolute_sums :
    (∑ i, |actualGapFunction (actualSourceInput i)|) ≤ 22 ∧
      (∑ i, |actualGaussianCross actualSourceInput (1/5) i|) ≤ 11 := by
  constructor
  · calc
      _ ≤ ∑ _i : Fin 11, (2:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hp : |(actualSourceInput i-1/20)*(actualSourceInput i-3/20)| ≤ 2 := by
          fin_cases i <;> norm_num [actualSourceInput]
        have he : Real.exp (-(actualSourceInput i)^2/2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (actualSourceInput i)])
        rw [actualGapFunction,abs_mul,abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ |(actualSourceInput i-1/20)*(actualSourceInput i-3/20)| * 1 :=
            mul_le_mul_of_nonneg_left he (abs_nonneg _)
          _ ≤ 2 := by simpa only [mul_one] using hp
      _ = _ := by simp
  · calc
      _ ≤ ∑ _i : Fin 11, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [actualGaussianCross,actualGaussianKernel,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (actualSourceInput i-1/5)])
      _ = _ := by simp

theorem actual_matrix_posterior_mean_and_variance_match_the_certified_rational_sums :
    |actualGaussianMean actualSourceInput (1/10000000000) (1/5)-
      (∑ i, actualWeightApproximation i*actualLabelApproximation i)| ≤ 1/1000000000000000 ∧
    |actualGaussianVariance actualSourceInput (1/10000000000) (1/5)-
      (1-∑ i, actualCrossApproximation i*actualWeightApproximation i)| ≤ 1/1000000000000000 := by
  have hw := actual_rational_approximate_weights_have_small_true_table_system_residuals.2
  have hd := actual_source_labels_and_cross_entries_have_small_absolute_sums
  constructor
  · rw [actual_literal_gp_mean_equals_the_true_source_coefficient_weighted_prediction
      actualSourceInput
      actual_source_eleven_noise_free_inputs_are_distinct_and_have_a_positive_definite_gaussian_gram.1
      (1/10000000000) (1/5) (by norm_num)]
    have h := actual_two_factor_finite_sum_error_has_separate_weight_and_data_bounds
      actualSourceWeight actualWeightApproximation (fun i => actualGapFunction (actualSourceInput i))
      actualLabelApproximation (4/1000000000000000000) (2/10000000000000000000000000000000)
      actual_inverse_matrix_weights_are_rigorously_close_to_the_rational_candidates
      actual_source_labels_have_rigorous_table_error_bounds
    change |(∑ i, actualSourceWeight i*actualGapFunction (actualSourceInput i))-
      (∑ i, actualWeightApproximation i*actualLabelApproximation i)| ≤ _
    linarith [hd.1]
  · have h := actual_two_factor_finite_sum_error_has_separate_weight_and_data_bounds
      actualSourceWeight actualWeightApproximation (actualGaussianCross actualSourceInput (1/5))
      actualCrossApproximation (4/1000000000000000000) (1/10000000000000000000000000000000)
      actual_inverse_matrix_weights_are_rigorously_close_to_the_rational_candidates
      actual_source_gram_and_cross_entries_have_rigorous_table_error_bounds.2
    have heq : actualGaussianVariance actualSourceInput (1/10000000000) (1/5)-
        (1-∑ i, actualCrossApproximation i*actualWeightApproximation i)=
      -((∑ i, actualSourceWeight i*actualGaussianCross actualSourceInput (1/5) i)-
        (∑ i, actualWeightApproximation i*actualCrossApproximation i)) := by
      simp only [actualGaussianVariance,CompleteModulesMatrixGP.posteriorVariance,
        actualSourceWeight,dotProduct]
      simp only [mul_comm]
      ring
    rw [heq,abs_neg]
    linarith [hd.2]

theorem actual_eleven_point_matrix_posterior_has_a_positive_lower_bound_rounding_to_point_zero_zero_six_seven :
    let lower := actualGaussianMean actualSourceInput (1/10000000000) (1/5)-
      Real.sqrt (326409/160000:ℝ)*Real.sqrt
        (actualGaussianVariance actualSourceInput (1/10000000000) (1/5))
    0 < lower ∧ |lower-(67/10000:ℝ)| < 1/20000 := by
  dsimp only
  have he := actual_matrix_posterior_mean_and_variance_match_the_certified_rational_sums
  have hn := actual_rational_approximate_prediction_and_variance_have_tight_enclosures
  have hm : (73479/10000000:ℝ) < actualGaussianMean actualSourceInput (1/10000000000) (1/5) ∧
      actualGaussianMean actualSourceInput (1/10000000000) (1/5) < 7348/1000000 := by
    have h := abs_le.mp he.1
    constructor <;> linarith [hn.1,hn.2.1]
  have hv : (19353/100000000000:ℝ) < actualGaussianVariance actualSourceInput (1/10000000000) (1/5) ∧
      actualGaussianVariance actualSourceInput (1/10000000000) (1/5) < 19354/100000000000 := by
    have h := abs_le.mp he.2
    constructor <;> linarith [hn.2.2.1,hn.2.2.2]
  have hvar : 0 ≤ actualGaussianVariance actualSourceInput (1/10000000000) (1/5) := by linarith [hv.1]
  have hs := Real.sq_sqrt hvar
  have hsn := Real.sqrt_nonneg (actualGaussianVariance actualSourceInput (1/10000000000) (1/5))
  have hsig : (4399/10000000:ℝ) < Real.sqrt (actualGaussianVariance actualSourceInput (1/10000000000) (1/5)) ∧
      Real.sqrt (actualGaussianVariance actualSourceInput (1/10000000000) (1/5)) < 11/25000 := by
    constructor <;> nlinarith [hv.1,hv.2]
  have hb := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 326409/160000)
  have hbn := Real.sqrt_nonneg (326409/160000:ℝ)
  have hB : (14283/10000:ℝ) < Real.sqrt (326409/160000:ℝ) ∧
      Real.sqrt (326409/160000:ℝ) < 3571/2500 := by
    constructor <;> nlinarith
  have hproductLower : (14283/10000:ℝ)*(4399/10000000) <
      Real.sqrt (326409/160000:ℝ)*Real.sqrt (actualGaussianVariance actualSourceInput (1/10000000000) (1/5)) :=
    mul_lt_mul hB.1 hsig.1.le (by norm_num) (by linarith [hB.1])
  have hproductUpper : Real.sqrt (326409/160000:ℝ)*
      Real.sqrt (actualGaussianVariance actualSourceInput (1/10000000000) (1/5)) <
      (3571/2500:ℝ)*(11/25000) :=
    mul_lt_mul hB.2 hsig.2.le hsn (by norm_num)
  constructor
  · linarith [hm.1]
  · rw [abs_lt]
    constructor <;> linarith [hm.1,hm.2]

theorem actual_source_eleven_point_gaussian_certificate_really_certifies_the_positive_right_point :
    0 ≤ actualGapFunction (1/5) := by
  apply actual_source_eleven_point_regularized_lower_bound_is_a_genuine_safe_certificate
  exact actual_eleven_point_matrix_posterior_has_a_positive_lower_bound_rounding_to_point_zero_zero_six_seven.1.le

end SafeLearning.CompleteModulesGaussianNumericConsequences
