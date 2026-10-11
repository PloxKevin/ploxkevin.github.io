import SafeLearning.CompleteAppliedGaussianBayesGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGPRepeatedBayes

def prefixVariance (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
def prefixMean (reading : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, reading i) / ((n : ℝ) + 1)
def prefixLikelihood (reading : ℕ → ℝ) (n : ℕ) (latent : ℝ) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, gaussianPDF latent 1 (reading i)
def prefixEvidence (reading : ℕ → ℝ) : ℕ → ℝ≥0∞
  | 0 => 1
  | n + 1 => prefixEvidence reading n *
      CompleteAppliedGaussianBayesGeneral.evidence (prefixMean reading n) (reading n) (prefixVariance n) 1
def weightedPrior (reading : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  (gaussianReal 0 1).withDensity (prefixLikelihood reading n)

theorem actual_each_source_repeated_measurement_precision_update_has_the_derived_parameters
    (reading : ℕ → ℝ) (n : ℕ) :
    CompleteAppliedGaussianBayesGeneral.posteriorMean (prefixMean reading n) (reading n) (prefixVariance n) 1 =
      prefixMean reading (n + 1) ∧
    CompleteAppliedGaussianBayesGeneral.posteriorVariance (prefixVariance n) 1 = prefixVariance (n + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hm : (n : ℝ) + 2 ≠ 0 := by positivity
  constructor
  · simp only [CompleteAppliedGaussianBayesGeneral.posteriorMean, prefixVariance, prefixMean, Finset.sum_range_succ,
      NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast, Nat.cast_add,
      Nat.cast_one]
    field_simp
    <;> ring
  · unfold CompleteAppliedGaussianBayesGeneral.posteriorVariance prefixVariance
    have hnn : (n : ℝ≥0) + 1 ≠ 0 := by positivity
    have hnm : (n : ℝ≥0) + 2 ≠ 0 := by positivity
    norm_num
    field_simp
    <;> ring

theorem actual_all_finite_independent_likelihood_products_have_the_derived_bayes_factorization
    (reading : ℕ → ℝ) (n : ℕ) (latent : ℝ) :
    gaussianPDF 0 1 latent * prefixLikelihood reading n latent =
      prefixEvidence reading n * gaussianPDF (prefixMean reading n) (prefixVariance n) latent := by
  induction n with
  | zero => simp [prefixLikelihood, prefixEvidence, prefixMean, prefixVariance]
  | succ n ih =>
    have hv : 0 < prefixVariance n := by unfold prefixVariance; positivity
    have h := CompleteAppliedGaussianBayesGeneral.actual_general_extended_gaussian_bayes_factorization
      (prefixMean reading n) (reading n) latent (prefixVariance n) 1 hv (by norm_num)
    have hp := actual_each_source_repeated_measurement_precision_update_has_the_derived_parameters
      reading n
    simp only [hp.1, hp.2] at h
    rw [prefixLikelihood, Finset.prod_range_succ, ← mul_assoc]
    change (gaussianPDF 0 1 latent * prefixLikelihood reading n latent) *
      gaussianPDF latent 1 (reading n) = _
    rw [ih, mul_assoc, h]
    simp only [prefixEvidence, mul_assoc]

theorem actual_all_finite_independent_likelihood_products_give_the_true_weighted_prior
    (reading : ℕ → ℝ) (n : ℕ) :
    weightedPrior reading n = prefixEvidence reading n •
      gaussianReal (prefixMean reading n) (prefixVariance n) := by
  have hv : prefixVariance n ≠ 0 := by unfold prefixVariance; positivity
  unfold weightedPrior
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    ← withDensity_mul volume (by fun_prop) (by unfold prefixLikelihood; fun_prop)]
  have hd : (gaussianPDF 0 1 * prefixLikelihood reading n) =
      (fun latent => prefixEvidence reading n *
        gaussianPDF (prefixMean reading n) (prefixVariance n) latent) := by
    funext latent
    exact actual_all_finite_independent_likelihood_products_have_the_derived_bayes_factorization
      reading n latent
  rw [hd, gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_smul _ (by fun_prop)

theorem actual_product_evidence_is_positive_finite_and_the_true_likelihood_integral
    (reading : ℕ → ℝ) (n : ℕ) :
    prefixEvidence reading n ≠ 0 ∧ prefixEvidence reading n ≠ ⊤ ∧
      (∫⁻ latent, prefixLikelihood reading n latent ∂ gaussianReal 0 1) =
        prefixEvidence reading n := by
  have hpos : prefixEvidence reading n ≠ 0 ∧ prefixEvidence reading n ≠ ⊤ := by
    induction n with
    | zero => simp [prefixEvidence]
    | succ n ih =>
      have he0 : CompleteAppliedGaussianBayesGeneral.evidence (prefixMean reading n) (reading n) (prefixVariance n) 1 ≠ 0 := by
        unfold CompleteAppliedGaussianBayesGeneral.evidence
        exact ne_of_gt (gaussianPDF_pos _ (by positivity) _)
      have het : CompleteAppliedGaussianBayesGeneral.evidence (prefixMean reading n) (reading n) (prefixVariance n) 1 ≠ ⊤ :=
        gaussianPDF_ne_top
      exact ⟨mul_ne_zero ih.1 he0, ENNReal.mul_ne_top ih.2 het⟩
  refine ⟨hpos.1, hpos.2, ?_⟩
  have h := congrArg (fun law : Measure ℝ => law Set.univ)
    (actual_all_finite_independent_likelihood_products_give_the_true_weighted_prior reading n)
  simpa [weightedPrior, withDensity_apply, Measure.smul_apply] using h

theorem actual_full_product_likelihood_normalized_posterior_has_variance_one_over_n_plus_one
    (reading : ℕ → ℝ) (n : ℕ) :
    (prefixEvidence reading n)⁻¹ • weightedPrior reading n =
      gaussianReal (prefixMean reading n) (prefixVariance n) := by
  have he := actual_product_evidence_is_positive_finite_and_the_true_likelihood_integral reading n
  rw [actual_all_finite_independent_likelihood_products_give_the_true_weighted_prior,
    smul_smul, ENNReal.inv_mul_cancel he.1 he.2.1, one_smul]

theorem actual_source_repeated_posterior_variances_strictly_decrease_with_diminishing_reductions
    (n : ℕ) :
    (prefixVariance (n + 1) : ℝ) < prefixVariance n ∧
      (prefixVariance n : ℝ) - prefixVariance (n + 1) =
        1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ∧
      (prefixVariance (n + 1) : ℝ) - prefixVariance (n + 2) <
        (prefixVariance n : ℝ) - prefixVariance (n + 1) := by
  simp only [prefixVariance, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm : 0 < (n : ℝ) + 2 := by positivity
  have hk : 0 < (n : ℝ) + 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · apply one_div_lt_one_div_of_lt hn
    linarith
  · field_simp
    <;> ring
  · field_simp
    norm_num at *
    nlinarith

theorem actual_source_repeated_posterior_variance_examples :
    prefixVariance 1 = (1 / 2 : ℝ≥0) ∧ prefixVariance 3 = (1 / 4 : ℝ≥0) := by
  norm_num [prefixVariance]

end SafeLearning.CompleteModulesGPRepeatedBayes
