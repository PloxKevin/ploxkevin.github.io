import SafeLearning.CompleteAppliedGaussianBayesGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianFourUpdate
open CompleteAppliedGaussianBayesGeneral

abbrev Readings := ℝ × (ℝ × (ℝ × ℝ))
def firstMean (y : Readings) : ℝ := 4*y.1/5
def secondMean (y : Readings) : ℝ := 4*(y.1+y.2.1)/9
def thirdMean (y : Readings) : ℝ := 4*(y.1+y.2.1+y.2.2.1)/13
def fourthMean (y : Readings) : ℝ := 4*(y.1+y.2.1+y.2.2.1+y.2.2.2)/17
def readingAverage (y : Readings) : ℝ := (y.1+y.2.1+y.2.2.1+y.2.2.2)/4
def readingsLikelihood (y : Readings) (latent : ℝ) : ℝ≥0∞ :=
  gaussianPDF latent (1/4) y.1 * gaussianPDF latent (1/4) y.2.1 *
    gaussianPDF latent (1/4) y.2.2.1 * gaussianPDF latent (1/4) y.2.2.2
def readingsEvidence (y : Readings) : ℝ≥0∞ :=
  gaussianPDF 0 (5/4) y.1 * gaussianPDF (firstMean y) (9/20) y.2.1 *
    gaussianPDF (secondMean y) (13/36) y.2.2.1 *
      gaussianPDF (thirdMean y) (17/52) y.2.2.2
def weightedPrior (y : Readings) : Measure ℝ :=
  (gaussianReal 0 1).withDensity (readingsLikelihood y)

theorem actual_four_precision_updates_have_the_derived_parameters (y : Readings) :
    posteriorMean 0 y.1 1 (1/4)=firstMean y ∧
      posteriorVariance 1 (1/4)=1/5 ∧
    posteriorMean (firstMean y) y.2.1 (1/5) (1/4)=secondMean y ∧
      posteriorVariance (1/5) (1/4)=1/9 ∧
    posteriorMean (secondMean y) y.2.2.1 (1/9) (1/4)=thirdMean y ∧
      posteriorVariance (1/9) (1/4)=1/13 ∧
    posteriorMean (thirdMean y) y.2.2.2 (1/13) (1/4)=fourthMean y ∧
      posteriorVariance (1/13) (1/4)=1/17 := by
  norm_num [posteriorMean,posteriorVariance,firstMean,secondMean,thirdMean,fourthMean]
  repeat' constructor
  all_goals ring

theorem actual_full_four_measurement_likelihood_has_the_derived_bayes_factorization
    (y : Readings) (latent : ℝ) :
    gaussianPDF 0 1 latent*readingsLikelihood y latent=
      readingsEvidence y*gaussianPDF (fourthMean y) (1/17) latent := by
  have h1:=actual_general_extended_gaussian_bayes_factorization 0 y.1 latent 1 (1/4)
    (by norm_num) (by norm_num)
  have h2:=actual_general_extended_gaussian_bayes_factorization (firstMean y) y.2.1 latent
    (1/5) (1/4) (by norm_num) (by norm_num)
  have h3:=actual_general_extended_gaussian_bayes_factorization (secondMean y) y.2.2.1 latent
    (1/9) (1/4) (by norm_num) (by norm_num)
  have h4:=actual_general_extended_gaussian_bayes_factorization (thirdMean y) y.2.2.2 latent
    (1/13) (1/4) (by norm_num) (by norm_num)
  have hp:=actual_four_precision_updates_have_the_derived_parameters y
  simp only [evidence,hp.1,hp.2.1] at h1
  simp only [evidence,hp.2.2.1,hp.2.2.2.1] at h2
  simp only [evidence,hp.2.2.2.2.1,hp.2.2.2.2.2.1] at h3
  simp only [evidence,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2] at h4
  norm_num at h1 h2 h3 h4
  unfold readingsLikelihood readingsEvidence
  calc
    _=(((gaussianPDF 0 1 latent*gaussianPDF latent (1/4) y.1)*
      gaussianPDF latent (1/4) y.2.1)*gaussianPDF latent (1/4) y.2.2.1)*
        gaussianPDF latent (1/4) y.2.2.2 := by ring
    _=(((gaussianPDF 0 (5/4) y.1*gaussianPDF (firstMean y) (1/5) latent)*
      gaussianPDF latent (1/4) y.2.1)*gaussianPDF latent (1/4) y.2.2.1)*
        gaussianPDF latent (1/4) y.2.2.2 := by rw [h1]
    _=(gaussianPDF 0 (5/4) y.1*(gaussianPDF (firstMean y) (1/5) latent*
      gaussianPDF latent (1/4) y.2.1))*gaussianPDF latent (1/4) y.2.2.1*
        gaussianPDF latent (1/4) y.2.2.2 := by ring
    _=(gaussianPDF 0 (5/4) y.1*(gaussianPDF (firstMean y) (9/20) y.2.1*
      gaussianPDF (secondMean y) (1/9) latent))*gaussianPDF latent (1/4) y.2.2.1*
        gaussianPDF latent (1/4) y.2.2.2 := by rw [h2]
    _=(gaussianPDF 0 (5/4) y.1*gaussianPDF (firstMean y) (9/20) y.2.1)*
      (gaussianPDF (secondMean y) (1/9) latent*gaussianPDF latent (1/4) y.2.2.1)*
        gaussianPDF latent (1/4) y.2.2.2 := by ring
    _=(gaussianPDF 0 (5/4) y.1*gaussianPDF (firstMean y) (9/20) y.2.1)*
      (gaussianPDF (secondMean y) (13/36) y.2.2.1*gaussianPDF (thirdMean y) (1/13) latent)*
        gaussianPDF latent (1/4) y.2.2.2 := by rw [h3]
    _=(gaussianPDF 0 (5/4) y.1*gaussianPDF (firstMean y) (9/20) y.2.1*
      gaussianPDF (secondMean y) (13/36) y.2.2.1)*
        (gaussianPDF (thirdMean y) (1/13) latent*gaussianPDF latent (1/4) y.2.2.2) := by ring
    _=(gaussianPDF 0 (5/4) y.1*gaussianPDF (firstMean y) (9/20) y.2.1*
      gaussianPDF (secondMean y) (13/36) y.2.2.1)*
        (gaussianPDF (thirdMean y) (17/52) y.2.2.2*gaussianPDF (fourthMean y) (1/17) latent) := by rw [h4]
    _=_ := by ring

theorem actual_full_data_weighted_prior_is_evidence_times_the_posterior (y : Readings) :
    weightedPrior y=readingsEvidence y • gaussianReal (fourthMean y) (1/17) := by
  unfold weightedPrior
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    ←withDensity_mul volume (by fun_prop) (by unfold readingsLikelihood;fun_prop)]
  have he : (gaussianPDF 0 1*readingsLikelihood y)=
      (fun latent=>readingsEvidence y*gaussianPDF (fourthMean y) (1/17) latent) := by
    funext latent
    exact actual_full_four_measurement_likelihood_has_the_derived_bayes_factorization y latent
  rw [he,gaussianReal_of_var_ne_zero _ (by norm_num)]
  exact withDensity_smul _ (by fun_prop)

theorem actual_full_data_evidence_is_the_true_likelihood_integral (y : Readings) :
    (∫⁻latent,readingsLikelihood y latent ∂gaussianReal 0 1)=readingsEvidence y := by
  have h:=congrArg (fun law:Measure ℝ=>law Set.univ)
    (actual_full_data_weighted_prior_is_evidence_times_the_posterior y)
  simpa [weightedPrior,withDensity_apply,Measure.smul_apply] using h

theorem actual_full_data_normalized_bayes_posterior_is_the_derived_gaussian (y : Readings) :
    (readingsEvidence y)⁻¹ • weightedPrior y=gaussianReal (fourthMean y) (1/17) := by
  have he0 : readingsEvidence y≠0 := by
    unfold readingsEvidence
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (ne_of_gt (gaussianPDF_pos _ (by norm_num) _))
      (ne_of_gt (gaussianPDF_pos _ (by norm_num) _)))
      (ne_of_gt (gaussianPDF_pos _ (by norm_num) _)))
      (ne_of_gt (gaussianPDF_pos _ (by norm_num) _))
  have het : readingsEvidence y≠⊤ := by
    unfold readingsEvidence
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top) gaussianPDF_ne_top) gaussianPDF_ne_top
  rw [actual_full_data_weighted_prior_is_evidence_times_the_posterior,
    smul_smul,ENNReal.inv_mul_cancel he0 het,one_smul]

theorem actual_all_four_readings_with_average_nine_tenths_have_the_literal_posterior
    (y : Readings) (hy : readingAverage y=9/10) :
    (readingsEvidence y)⁻¹ • weightedPrior y=gaussianReal (72/85) (1/17) := by
  rw [actual_full_data_normalized_bayes_posterior_is_the_derived_gaussian]
  have hm : fourthMean y=72/85 := by
    unfold readingAverage at hy
    unfold fourthMean
    linarith
  rw [hm]

end SafeLearning.CompleteAppliedGaussianFourUpdate
