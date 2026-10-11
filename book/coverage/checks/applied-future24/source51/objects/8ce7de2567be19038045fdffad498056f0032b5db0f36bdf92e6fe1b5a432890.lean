import SafeLearning.CompleteAppliedGaussianPosteriorJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedGaussianPosteriorGenerative
open CompleteAppliedGaussianPosterior CompleteAppliedGaussianPosteriorJoint

def priorNoiseToObservation (pair : ℝ × ℝ) : ℝ × ℝ := (pair.1,pair.1+pair.2)

theorem actual_independent_prior_and_noise_construct_the_same_generative_joint :
    (sourcePrior.prod (gaussianReal 0 1)).map priorNoiseToObservation=actualGenerativeJoint := by
  have hmap : Measurable priorNoiseToObservation := by
    unfold priorNoiseToObservation;fun_prop
  have : IsProbabilityMeasure sourcePrior := by
    change IsProbabilityMeasure (gaussianReal 0 4);infer_instance
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest hmap]
  change (∫⁻ a,(test ∘ priorNoiseToObservation) a ∂sourcePrior.prod (gaussianReal 0 1))=_
  rw [lintegral_prod _ (htest.comp hmap).aemeasurable]
  rw [actualGenerativeJoint,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro latent
  have ht : Measurable (fun reading => test (latent,reading)) :=
    htest.comp measurable_prodMk_left
  have hm : (gaussianReal 0 1).map (latent+·)=observationKernel latent := by
    rw [gaussianReal_map_const_add]
    simp [observationKernel]
  have hi := lintegral_map ht (show Measurable (fun reading : ℝ => latent+reading) by fun_prop)
    (μ := gaussianReal 0 1)
  rw [hm] at hi
  simpa only [priorNoiseToObservation,Function.comp_def] using hi.symm

theorem actual_independent_measurement_model_has_the_true_joint_and_posterior_disintegration
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {latent noise : Ω → ℝ} (hlatent : HasLaw latent sourcePrior mu)
    (hnoise : HasLaw noise (gaussianReal 0 1) mu) (hindep : IndepFun latent noise mu) :
    HasLaw (fun omega => (latent omega,latent omega+noise omega)) actualGenerativeJoint mu ∧
      HasLaw (fun omega => (latent omega+noise omega,latent omega))
        (gaussianReal 0 5 ⊗ₘ posteriorKernel) mu := by
  have hpair := hindep.hasLaw_prod hlatent hnoise
  have hgenerative : HasLaw priorNoiseToObservation actualGenerativeJoint
      (sourcePrior.prod (gaussianReal 0 1)) :=
    ⟨(show Measurable priorNoiseToObservation by unfold priorNoiseToObservation;fun_prop).aemeasurable,
      actual_independent_prior_and_noise_construct_the_same_generative_joint⟩
  have hforward := hgenerative.comp hpair
  have hswap : HasLaw Prod.swap (gaussianReal 0 5 ⊗ₘ posteriorKernel)
      actualGenerativeJoint :=
    ⟨measurable_swap.aemeasurable,
      actual_reversed_joint_is_the_evidence_law_times_the_derived_posterior_kernel⟩
  exact ⟨hforward,hswap.comp hforward⟩

end SafeLearning.CompleteAppliedGaussianPosteriorGenerative
