import SafeLearning.CompleteAppliedGaussianBayesGeneral
import SafeLearning.CompleteAppliedGaussianPosteriorJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianBayesJoint
open CompleteAppliedGaussianBayesGeneral

def observationKernel (noiseVariance : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨fun latent=>gaussianReal latent noiseVariance,by fun_prop⟩
def posteriorKernel (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨fun reading=>gaussianReal (posteriorMean priorMean reading priorVariance noiseVariance)
    (posteriorVariance priorVariance noiseVariance),by dsimp [posteriorMean];fun_prop⟩
instance observationKernel_markov (noiseVariance : ℝ≥0) : IsMarkovKernel (observationKernel noiseVariance) :=
  ⟨fun _=>by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩
instance posteriorKernel_markov (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0) :
    IsMarkovKernel (posteriorKernel priorMean priorVariance noiseVariance) :=
  ⟨fun _=>by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩

def actualJoint (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0) : Measure (ℝ×ℝ) :=
  gaussianReal priorMean priorVariance ⊗ₘ observationKernel noiseVariance

theorem actual_observation_kernel_has_its_true_gaussian_likelihood_density
    (noiseVariance : ℝ≥0) (hw : 0<noiseVariance) :
    observationKernel noiseVariance=(Kernel.const ℝ volume).withDensity
      (fun latent reading=>gaussianPDF latent noiseVariance reading) := by
  ext latent event hevent
  rw [Kernel.withDensity_apply' _ (by fun_prop),Kernel.const_apply]
  change gaussianReal latent noiseVariance event=_
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt hw),withDensity_apply _ hevent]

theorem actual_posterior_kernel_has_its_derived_gaussian_density
    (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    posteriorKernel priorMean priorVariance noiseVariance=(Kernel.const ℝ volume).withDensity
      (fun reading latent=>gaussianPDF (posteriorMean priorMean reading priorVariance noiseVariance)
        (posteriorVariance priorVariance noiseVariance) latent) := by
  have hp : posteriorVariance priorVariance noiseVariance≠0 := by unfold posteriorVariance;positivity
  ext reading event hevent
  rw [Kernel.withDensity_apply' _ (by dsimp [posteriorMean];fun_prop),Kernel.const_apply]
  change gaussianReal (posteriorMean priorMean reading priorVariance noiseVariance)
    (posteriorVariance priorVariance noiseVariance) event=_
  rw [gaussianReal_of_var_ne_zero _ hp,withDensity_apply _ hevent]

theorem actual_general_generative_joint_has_the_prior_likelihood_product_density
    (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    actualJoint priorMean priorVariance noiseVariance=(volume.prod volume).withDensity
      (fun pair=>gaussianPDF priorMean priorVariance pair.1*gaussianPDF pair.1 noiseVariance pair.2) := by
  have : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun latent reading=>gaussianPDF latent noiseVariance reading)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>gaussianPDF_ne_top)
  rw [actualJoint,actual_observation_kernel_has_its_true_gaussian_likelihood_density _ hw,
    gaussianReal_of_var_ne_zero _ (ne_of_gt hv),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop),Measure.compProd_const]

theorem actual_reversed_generative_joint_is_the_true_evidence_and_derived_posterior_disintegration
    (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance) :
    (actualJoint priorMean priorVariance noiseVariance).map Prod.swap=
      gaussianReal priorMean (priorVariance+noiseVariance) ⊗ₘ
        posteriorKernel priorMean priorVariance noiseVariance := by
  have : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun reading latent=>gaussianPDF (posteriorMean priorMean reading priorVariance noiseVariance)
        (posteriorVariance priorVariance noiseVariance) latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>gaussianPDF_ne_top)
  rw [actual_general_generative_joint_has_the_prior_likelihood_product_density _ _ _ hv hw,
    CompleteAppliedGaussianPosteriorJoint.actual_swap_of_product_volume_with_density _ (by fun_prop),
    actual_posterior_kernel_has_its_derived_gaussian_density _ _ _ hv hw,
    gaussianReal_of_var_ne_zero _ (by positivity),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by dsimp [posteriorMean];fun_prop),
    Measure.compProd_const]
  apply congrArg (fun density=>(volume.prod volume).withDensity density)
  funext pair
  exact actual_general_extended_gaussian_bayes_factorization _ _ _ _ _ hv hw

theorem actual_independent_prior_noise_pair_constructs_the_same_joint
    (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0) :
    ((gaussianReal priorMean priorVariance).prod (gaussianReal 0 noiseVariance)).map
      (fun pair:ℝ×ℝ=>(pair.1,pair.1+pair.2))=actualJoint priorMean priorVariance noiseVariance := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻a,(test ∘ (fun pair:ℝ×ℝ=>(pair.1,pair.1+pair.2))) a
    ∂(gaussianReal priorMean priorVariance).prod (gaussianReal 0 noiseVariance))=_
  rw [lintegral_prod _ (by fun_prop),actualJoint,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro latent
  have ht : Measurable (fun reading=>test (latent,reading)) := htest.comp measurable_prodMk_left
  have hm : (gaussianReal 0 noiseVariance).map (latent+·)=observationKernel noiseVariance latent := by
    rw [gaussianReal_map_const_add]
    simp [observationKernel]
  have hi := lintegral_map ht (show Measurable (fun reading:ℝ=>latent+reading) by fun_prop)
    (μ:=gaussianReal 0 noiseVariance)
  rw [hm] at hi
  simpa only [Function.comp_def] using hi.symm

theorem actual_arbitrary_independent_gaussian_model_has_the_derived_joint_and_conditional_kernel
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {latent noise : Ω→ℝ} (priorMean : ℝ) (priorVariance noiseVariance : ℝ≥0)
    (hv : 0<priorVariance) (hw : 0<noiseVariance)
    (hlatent : HasLaw latent (gaussianReal priorMean priorVariance) P)
    (hnoise : HasLaw noise (gaussianReal 0 noiseVariance) P)
    (hindep : IndepFun latent noise P) :
    HasLaw (fun omega=>(latent omega+noise omega,latent omega))
      (gaussianReal priorMean (priorVariance+noiseVariance) ⊗ₘ
        posteriorKernel priorMean priorVariance noiseVariance) P := by
  have hpair := hindep.hasLaw_prod hlatent hnoise
  have hgenerative : HasLaw (fun pair:ℝ×ℝ=>(pair.1,pair.1+pair.2))
      (actualJoint priorMean priorVariance noiseVariance)
      ((gaussianReal priorMean priorVariance).prod (gaussianReal 0 noiseVariance)) :=
    ⟨(show Measurable (fun pair:ℝ×ℝ=>(pair.1,pair.1+pair.2)) by fun_prop).aemeasurable,
      actual_independent_prior_noise_pair_constructs_the_same_joint _ _ _⟩
  have hforward := hgenerative.comp hpair
  have hswap : HasLaw Prod.swap
      (gaussianReal priorMean (priorVariance+noiseVariance) ⊗ₘ posteriorKernel priorMean priorVariance noiseVariance)
      (actualJoint priorMean priorVariance noiseVariance) :=
    ⟨measurable_swap.aemeasurable,
      actual_reversed_generative_joint_is_the_true_evidence_and_derived_posterior_disintegration _ _ _ hv hw⟩
  exact hswap.comp hforward

end SafeLearning.CompleteAppliedGaussianBayesJoint
