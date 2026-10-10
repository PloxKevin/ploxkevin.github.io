import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedGaussianBayesGeneral

def posteriorMean (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0) : ℝ :=
  ((noiseVariance:ℝ)*priorMean+(priorVariance:ℝ)*reading)/(priorVariance+noiseVariance:ℝ≥0)
def posteriorVariance (priorVariance noiseVariance : ℝ≥0) : ℝ≥0 :=
  priorVariance*noiseVariance/(priorVariance+noiseVariance)
def likelihoodWeightedPrior (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0) : Measure ℝ :=
  (gaussianReal priorMean priorVariance).withDensity (fun latent=>gaussianPDF latent noiseVariance reading)
def evidence (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0) : ℝ≥0∞ :=
  gaussianPDF priorMean (priorVariance+noiseVariance) reading

theorem actual_general_gaussian_prior_likelihood_product_is_the_bayes_factorization
    (priorMean reading latent : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    gaussianPDFReal priorMean priorVariance latent*gaussianPDFReal latent noiseVariance reading=
      gaussianPDFReal priorMean (priorVariance+noiseVariance) reading*
        gaussianPDFReal (posteriorMean priorMean reading priorVariance noiseVariance)
          (posteriorVariance priorVariance noiseVariance) latent := by
  have hv0 : (priorVariance:ℝ)≠0 := ne_of_gt hv
  have hw0 : (noiseVariance:ℝ)≠0 := ne_of_gt hw
  have hd : (priorVariance:ℝ)+(noiseVariance:ℝ)≠0 := by positivity
  have hconstant : Real.sqrt (2*Real.pi*(priorVariance:ℝ))*Real.sqrt (2*Real.pi*(noiseVariance:ℝ))=
      Real.sqrt (2*Real.pi*((priorVariance:ℝ)+(noiseVariance:ℝ)))*
        Real.sqrt (2*Real.pi*((priorVariance:ℝ)*(noiseVariance:ℝ)/((priorVariance:ℝ)+(noiseVariance:ℝ)))) := by
    rw [←Real.sqrt_mul (by positivity),←Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexponent : -(latent-priorMean)^2/(2*(priorVariance:ℝ))+
      -(reading-latent)^2/(2*(noiseVariance:ℝ))=
      -(reading-priorMean)^2/(2*((priorVariance:ℝ)+(noiseVariance:ℝ)))+
        -(latent-(((noiseVariance:ℝ)*priorMean+(priorVariance:ℝ)*reading)/((priorVariance:ℝ)+(noiseVariance:ℝ))))^2/
          (2*((priorVariance:ℝ)*(noiseVariance:ℝ)/((priorVariance:ℝ)+(noiseVariance:ℝ)))) := by
    field_simp
    <;> ring
  simp only [gaussianPDFReal,posteriorMean,posteriorVariance,NNReal.coe_add,NNReal.coe_div,NNReal.coe_mul]
  calc
    _=(Real.sqrt (2*Real.pi*(priorVariance:ℝ))*Real.sqrt (2*Real.pi*(noiseVariance:ℝ)))⁻¹*
      Real.exp (-(latent-priorMean)^2/(2*(priorVariance:ℝ))+-(reading-latent)^2/(2*(noiseVariance:ℝ))) := by
        rw [Real.exp_add,mul_inv_rev];ring
    _=(Real.sqrt (2*Real.pi*((priorVariance:ℝ)+(noiseVariance:ℝ)))*
      Real.sqrt (2*Real.pi*((priorVariance:ℝ)*(noiseVariance:ℝ)/((priorVariance:ℝ)+(noiseVariance:ℝ)))))⁻¹*
      Real.exp (-(reading-priorMean)^2/(2*((priorVariance:ℝ)+(noiseVariance:ℝ)))+
        -(latent-(((noiseVariance:ℝ)*priorMean+(priorVariance:ℝ)*reading)/((priorVariance:ℝ)+(noiseVariance:ℝ))))^2/
          (2*((priorVariance:ℝ)*(noiseVariance:ℝ)/((priorVariance:ℝ)+(noiseVariance:ℝ))))) := by
        rw [hconstant,hexponent]
    _=_ := by rw [Real.exp_add,mul_inv_rev];ring

theorem actual_general_extended_gaussian_bayes_factorization
    (priorMean reading latent : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    gaussianPDF priorMean priorVariance latent*gaussianPDF latent noiseVariance reading=
      evidence priorMean reading priorVariance noiseVariance*
        gaussianPDF (posteriorMean priorMean reading priorVariance noiseVariance)
          (posteriorVariance priorVariance noiseVariance) latent := by
  dsimp [evidence,gaussianPDF]
  rw [←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    actual_general_gaussian_prior_likelihood_product_is_the_bayes_factorization _ _ _ _ _ hv hw]

theorem actual_general_weighted_prior_is_evidence_times_the_derived_posterior
    (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    likelihoodWeightedPrior priorMean reading priorVariance noiseVariance=
      evidence priorMean reading priorVariance noiseVariance •
        gaussianReal (posteriorMean priorMean reading priorVariance noiseVariance)
          (posteriorVariance priorVariance noiseVariance) := by
  have hpost : posteriorVariance priorVariance noiseVariance≠0 := by
    unfold posteriorVariance;positivity
  unfold likelihoodWeightedPrior
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt hv),
    ←withDensity_mul volume (by fun_prop) (by fun_prop)]
  have he : (gaussianPDF priorMean priorVariance*fun latent=>gaussianPDF latent noiseVariance reading)=
      (fun latent=>evidence priorMean reading priorVariance noiseVariance*
        gaussianPDF (posteriorMean priorMean reading priorVariance noiseVariance)
          (posteriorVariance priorVariance noiseVariance) latent) := by
    funext latent
    exact actual_general_extended_gaussian_bayes_factorization _ _ _ _ _ hv hw
  rw [he,gaussianReal_of_var_ne_zero _ hpost]
  exact withDensity_smul _ (by fun_prop)

theorem actual_general_evidence_is_the_true_likelihood_integral
    (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    (∫⁻latent,gaussianPDF latent noiseVariance reading ∂gaussianReal priorMean priorVariance)=
      evidence priorMean reading priorVariance noiseVariance := by
  have h := congrArg (fun law:Measure ℝ=>law Set.univ)
    (actual_general_weighted_prior_is_evidence_times_the_derived_posterior
      priorMean reading priorVariance noiseVariance hv hw)
  simpa [likelihoodWeightedPrior,withDensity_apply,Measure.smul_apply] using h

theorem actual_general_normalized_likelihood_posterior_is_the_derived_gaussian
    (priorMean reading : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    (evidence priorMean reading priorVariance noiseVariance)⁻¹ •
      likelihoodWeightedPrior priorMean reading priorVariance noiseVariance=
        gaussianReal (posteriorMean priorMean reading priorVariance noiseVariance)
          (posteriorVariance priorVariance noiseVariance) := by
  have he0 : evidence priorMean reading priorVariance noiseVariance≠0 := by
    unfold evidence
    exact ne_of_gt (gaussianPDF_pos _ (by positivity) _)
  have het : evidence priorMean reading priorVariance noiseVariance≠⊤ := gaussianPDF_ne_top
  rw [actual_general_weighted_prior_is_evidence_times_the_derived_posterior _ _ _ _ hv hw,
    smul_smul,ENNReal.inv_mul_cancel he0 het,one_smul]

end SafeLearning.CompleteAppliedGaussianBayesGeneral
