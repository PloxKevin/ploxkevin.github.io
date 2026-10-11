import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedGaussianPosterior

def sourcePrior : Measure ℝ := gaussianReal 0 4
def sourceLikelihood (latent reading : ℝ) : ℝ≥0∞ := gaussianPDF latent 1 reading
def sourceEvidenceDensity (reading : ℝ) : ℝ≥0∞ := gaussianPDF 0 5 reading
def sourceUnnormalizedPosterior (reading : ℝ) : Measure ℝ :=
  sourcePrior.withDensity (fun latent => sourceLikelihood latent reading)
def sourcePosterior (reading : ℝ) : Measure ℝ :=
  (sourceEvidenceDensity reading)⁻¹ • sourceUnnormalizedPosterior reading

theorem actual_prior_likelihood_product_is_the_exact_gaussian_bayes_factorization
    (latent reading : ℝ) :
    gaussianPDFReal 0 4 latent*gaussianPDFReal latent 1 reading=
      gaussianPDFReal 0 5 reading*gaussianPDFReal ((4/5)*reading) (4/5) latent := by
  have hconstant : Real.sqrt (2*Real.pi*4)*Real.sqrt (2*Real.pi*1)=
      Real.sqrt (2*Real.pi*5)*Real.sqrt (2*Real.pi*(4/5)) := by
    rw [← Real.sqrt_mul (by positivity),← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hexponent : -(latent-0)^2/(2*4)+-(reading-latent)^2/(2*1)=
      -(reading-0)^2/(2*5)+-(latent-(4/5)*reading)^2/(2*(4/5)) := by ring
  simp only [gaussianPDFReal,NNReal.coe_ofNat,NNReal.coe_div,NNReal.coe_one]
  calc
    _=(Real.sqrt (2*Real.pi*4)*Real.sqrt (2*Real.pi*1))⁻¹*
      Real.exp (-(latent-0)^2/(2*4)+-(reading-latent)^2/(2*1)) := by
        rw [Real.exp_add,mul_inv_rev];ring
    _=(Real.sqrt (2*Real.pi*5)*Real.sqrt (2*Real.pi*(4/5)))⁻¹*
      Real.exp (-(reading-0)^2/(2*5)+-(latent-(4/5)*reading)^2/(2*(4/5))) := by
        rw [hconstant,hexponent]
    _=_ := by rw [Real.exp_add,mul_inv_rev];ring

theorem actual_extended_density_bayes_factorization (latent reading : ℝ) :
    gaussianPDF 0 4 latent*sourceLikelihood latent reading=
      sourceEvidenceDensity reading*gaussianPDF ((4/5)*reading) (4/5) latent := by
  dsimp [sourceLikelihood,sourceEvidenceDensity,gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    actual_prior_likelihood_product_is_the_exact_gaussian_bayes_factorization]

theorem actual_likelihood_weighted_prior_is_the_evidence_times_gaussian_posterior
    (reading : ℝ) :
    sourceUnnormalizedPosterior reading=
      sourceEvidenceDensity reading • gaussianReal ((4/5)*reading) (4/5) := by
  unfold sourceUnnormalizedPosterior sourcePrior
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    ← withDensity_mul volume (by fun_prop) (by
      dsimp [sourceLikelihood];fun_prop)]
  have he : (gaussianPDF 0 4 * fun latent => sourceLikelihood latent reading)=
      fun latent => sourceEvidenceDensity reading*gaussianPDF ((4/5)*reading) (4/5) latent := by
    funext latent
    exact actual_extended_density_bayes_factorization latent reading
  rw [he,gaussianReal_of_var_ne_zero _ (by norm_num)]
  exact withDensity_smul _ (by fun_prop)

theorem actual_evidence_is_the_integral_of_the_likelihood_under_the_actual_prior
    (reading : ℝ) :
    (∫⁻ latent,sourceLikelihood latent reading ∂sourcePrior)=sourceEvidenceDensity reading := by
  have h := congrArg (fun mu : Measure ℝ => mu Set.univ)
    (actual_likelihood_weighted_prior_is_the_evidence_times_gaussian_posterior reading)
  simpa [sourceUnnormalizedPosterior,withDensity_apply,Measure.smul_apply] using h

theorem actual_normalized_bayes_posterior_is_the_derived_gaussian_for_every_reading
    (reading : ℝ) : sourcePosterior reading=gaussianReal ((4/5)*reading) (4/5) := by
  have hn : sourceEvidenceDensity reading≠0 := by
    dsimp [sourceEvidenceDensity]
    exact ne_of_gt (gaussianPDF_pos _ (by norm_num) _)
  have ht : sourceEvidenceDensity reading≠⊤ := by
    exact gaussianPDF_ne_top
  rw [sourcePosterior,actual_likelihood_weighted_prior_is_the_evidence_times_gaussian_posterior,
    smul_smul,ENNReal.inv_mul_cancel hn ht,one_smul]

theorem actual_source_one_measurement_posterior_parameters_and_position :
    sourcePosterior 3=gaussianReal (12/5) (4/5) ∧
    (∫ latent : ℝ,latent ∂sourcePosterior 3)=12/5 ∧
    Var[fun latent : ℝ => latent;sourcePosterior 3]=4/5 ∧
    (0:ℝ)<12/5 ∧ (12/5:ℝ)<3 ∧ |(12/5:ℝ)-3| < |(12/5:ℝ)-0| ∧
    (1/4:ℝ)+1=5/4 ∧ (5/4:ℝ)⁻¹=4/5 := by
  have he : sourcePosterior 3=gaussianReal (12/5) (4/5) := by
    rw [actual_normalized_bayes_posterior_is_the_derived_gaussian_for_every_reading]
    norm_num
  rw [he,integral_id_gaussianReal,variance_fun_id_gaussianReal]
  norm_num

theorem actual_independent_future_noise_adds_variance_to_the_actual_posterior
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {latent noise : Ω → ℝ}
    (hlatent : HasLaw latent (sourcePosterior 3) mu)
    (hnoise : HasLaw noise (gaussianReal 0 1) mu)
    (hindep : IndepFun latent noise mu) :
    HasLaw (fun omega => latent omega+noise omega) (gaussianReal (12/5) (9/5)) mu ∧
      Var[fun omega => latent omega+noise omega;mu]=9/5 := by
  rw [actual_source_one_measurement_posterior_parameters_and_position.1] at hlatent
  have he := gaussianReal_add_gaussianReal_of_indepFun hindep hlatent hnoise
  have hl : HasLaw (fun omega => latent omega+noise omega)
      (gaussianReal (12/5) (9/5)) mu := by
    constructor
    · exact hlatent.aemeasurable.add hnoise.aemeasurable
    · norm_num at he
      exact he
  constructor
  · exact hl
  · rw [hl.variance_eq,variance_id_gaussianReal]
    norm_num

end SafeLearning.CompleteAppliedGaussianPosterior
