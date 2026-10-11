import SafeLearning.CompleteAppliedGaussianBayesJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedSequentialCalibration
open CompleteAppliedGaussianBayesGeneral

def readingsLikelihood (first second latent : ℝ) : ℝ≥0∞ :=
  gaussianPDF latent 1 first * gaussianPDF latent 4 second
def weightedPrior (first second : ℝ) : Measure ℝ :=
  (gaussianReal 0 4).withDensity (readingsLikelihood first second)
def readingsEvidence (first second : ℝ) : ℝ≥0∞ :=
  gaussianPDF 0 5 first * gaussianPDF (4*first/5) (24/5) second
def calibratedMean (first second : ℝ) : ℝ := (4*first+second)/6

theorem actual_first_and_second_gaussian_updates_have_the_derived_parameters
    (first second : ℝ) :
    posteriorMean 0 first 4 1=4*first/5 ∧ posteriorVariance 4 1=4/5 ∧
    posteriorMean (4*first/5) second (4/5) 4=calibratedMean first second ∧
    posteriorVariance (4/5) 4=2/3 := by
  simp only [posteriorMean,posteriorVariance,calibratedMean,NNReal.coe_add,NNReal.coe_div,
    NNReal.coe_ofNat]
  norm_num
  ring

theorem actual_independent_two_likelihood_product_has_the_derived_bayes_factorization
    (first second latent : ℝ) :
    gaussianPDF 0 4 latent*readingsLikelihood first second latent=
      readingsEvidence first second*gaussianPDF (calibratedMean first second) (2/3) latent := by
  have hfirst := actual_general_extended_gaussian_bayes_factorization 0 first latent 4 1
    (by norm_num) (by norm_num)
  have hsecond := actual_general_extended_gaussian_bayes_factorization (4*first/5) second latent
    (4/5) 4 (by norm_num) (by norm_num)
  have hp := actual_first_and_second_gaussian_updates_have_the_derived_parameters first second
  simp only [evidence,hp.1,hp.2.1] at hfirst
  simp only [evidence,hp.2.2.1,hp.2.2.2] at hsecond
  norm_num at hfirst hsecond
  unfold readingsLikelihood readingsEvidence
  calc
    _=(gaussianPDF 0 4 latent*gaussianPDF latent 1 first)*gaussianPDF latent 4 second := by ring
    _=(gaussianPDF 0 5 first*gaussianPDF (4*first/5) (4/5) latent)*gaussianPDF latent 4 second := by rw [hfirst]
    _=gaussianPDF 0 5 first*(gaussianPDF (4*first/5) (4/5) latent*gaussianPDF latent 4 second) := by ring
    _=gaussianPDF 0 5 first*(gaussianPDF (4*first/5) (24/5) second*
      gaussianPDF (calibratedMean first second) (2/3) latent) := by rw [hsecond]
    _=_ := by ring

theorem actual_two_reading_weighted_prior_is_evidence_times_the_posterior
    (first second : ℝ) :
    weightedPrior first second=readingsEvidence first second •
      gaussianReal (calibratedMean first second) (2/3) := by
  unfold weightedPrior
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    ←withDensity_mul volume (by fun_prop) (by unfold readingsLikelihood;fun_prop)]
  have he : (gaussianPDF 0 4*readingsLikelihood first second)=
      (fun latent=>readingsEvidence first second*
        gaussianPDF (calibratedMean first second) (2/3) latent) := by
    funext latent
    exact actual_independent_two_likelihood_product_has_the_derived_bayes_factorization _ _ _
  rw [he,gaussianReal_of_var_ne_zero _ (by norm_num)]
  exact withDensity_smul _ (by fun_prop)

theorem actual_reading_pair_evidence_is_the_true_likelihood_integral
    (first second : ℝ) :
    (∫⁻latent,readingsLikelihood first second latent ∂gaussianReal 0 4)=
      readingsEvidence first second := by
  have h := congrArg (fun law:Measure ℝ=>law Set.univ)
    (actual_two_reading_weighted_prior_is_evidence_times_the_posterior first second)
  simpa [weightedPrior,withDensity_apply,Measure.smul_apply] using h

theorem actual_normalized_two_reading_posterior_is_the_derived_gaussian
    (first second : ℝ) :
    (readingsEvidence first second)⁻¹ • weightedPrior first second=
      gaussianReal (calibratedMean first second) (2/3) := by
  have he0 : readingsEvidence first second≠0 := by
    unfold readingsEvidence
    exact mul_ne_zero (ne_of_gt (gaussianPDF_pos _ (by norm_num) _))
      (ne_of_gt (gaussianPDF_pos _ (by norm_num) _))
  have het : readingsEvidence first second≠⊤ := by
    unfold readingsEvidence
    exact ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top
  rw [actual_two_reading_weighted_prior_is_evidence_times_the_posterior,
    smul_smul,ENNReal.inv_mul_cancel he0 het,one_smul]

theorem actual_observed_two_reading_posterior_has_mean_seven_sixths_and_variance_two_thirds :
    (readingsEvidence 2 (-1))⁻¹ • weightedPrior 2 (-1)=gaussianReal (7/6) (2/3) := by
  convert actual_normalized_two_reading_posterior_is_the_derived_gaussian 2 (-1) using 1 <;>
    norm_num [calibratedMean]

theorem actual_offset_correction_has_zero_mean_gaussian_error :
    (gaussianReal (7/6) (2/3)).map (fun offset:ℝ=>offset-7/6)=gaussianReal 0 (2/3) := by
  have h := gaussianReal_map_add_const (μ:=7/6) (v:=2/3) (-7/6)
  convert h using 1 <;> norm_num [sub_eq_add_neg]

end SafeLearning.CompleteAppliedSequentialCalibration
