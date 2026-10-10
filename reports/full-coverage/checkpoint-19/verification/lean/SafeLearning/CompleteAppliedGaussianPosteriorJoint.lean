import SafeLearning.CompleteAppliedGaussianPosterior

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianPosteriorJoint
open CompleteAppliedGaussianPosterior

def observationKernel : Kernel ℝ ℝ := ⟨fun latent => gaussianReal latent 1,by fun_prop⟩
def posteriorKernel : Kernel ℝ ℝ := ⟨fun reading => gaussianReal ((4/5)*reading) (4/5),by fun_prop⟩

instance observationKernel_markov : IsMarkovKernel observationKernel := ⟨fun _ => by
  change IsProbabilityMeasure (gaussianReal _ 1);infer_instance⟩
instance posteriorKernel_markov : IsMarkovKernel posteriorKernel := ⟨fun _ => by
  change IsProbabilityMeasure (gaussianReal _ (4/5));infer_instance⟩

def actualGenerativeJoint : Measure (ℝ × ℝ) := sourcePrior ⊗ₘ observationKernel

instance actualGenerativeJoint_probability : IsProbabilityMeasure actualGenerativeJoint := by
  change IsProbabilityMeasure (gaussianReal 0 4 ⊗ₘ observationKernel)
  infer_instance

theorem actual_swap_of_product_volume_with_density (density : ℝ × ℝ → ℝ≥0∞)
    (hd : Measurable density) :
    ((volume.prod volume).withDensity density).map Prod.swap=
      (volume.prod volume).withDensity (fun pair => density pair.swap) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_swap]
  change (∫⁻ a, (test ∘ Prod.swap) a ∂(volume.prod volume).withDensity density)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (htest.comp measurable_swap)]
  change _=(∫⁻ a,test a ∂(volume.prod volume).withDensity (density ∘ Prod.swap))
  rw [lintegral_withDensity_eq_lintegral_mul _ (hd.comp measurable_swap) htest]
  have ht : Measurable (fun pair : ℝ × ℝ => density pair.swap*test pair) :=
    (hd.comp measurable_swap).mul htest
  have h := lintegral_map ht measurable_swap (μ := volume.prod volume)
  rw [Measure.prod_swap] at h
  simpa only [Prod.swap_swap,Function.comp_def,Pi.mul_apply] using h.symm

theorem actual_observation_kernel_has_the_true_likelihood_density :
    observationKernel=(Kernel.const ℝ volume).withDensity (fun latent reading => sourceLikelihood latent reading) := by
  ext latent event hevent
  rw [Kernel.withDensity_apply' _ (by dsimp [sourceLikelihood];fun_prop),Kernel.const_apply]
  change gaussianReal latent 1 event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),withDensity_apply _ hevent]
  rfl

theorem actual_posterior_kernel_has_the_true_gaussian_density :
    posteriorKernel=(Kernel.const ℝ volume).withDensity
      (fun reading latent => gaussianPDF ((4/5)*reading) (4/5) latent) := by
  ext reading event hevent
  rw [Kernel.withDensity_apply' _ (by fun_prop),Kernel.const_apply]
  change gaussianReal ((4/5)*reading) (4/5) event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),withDensity_apply _ hevent]

theorem actual_generative_joint_has_the_prior_times_likelihood_product_density :
    actualGenerativeJoint=(volume.prod volume).withDensity
      (fun pair => gaussianPDF 0 4 pair.1*sourceLikelihood pair.1 pair.2) := by
  have : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun latent reading => sourceLikelihood latent reading)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => gaussianPDF_ne_top)
  rw [actualGenerativeJoint,actual_observation_kernel_has_the_true_likelihood_density,
    sourcePrior,gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by dsimp [sourceLikelihood];fun_prop),
    Measure.compProd_const]

theorem actual_reversed_joint_is_the_evidence_law_times_the_derived_posterior_kernel :
    actualGenerativeJoint.map Prod.swap=gaussianReal 0 5 ⊗ₘ posteriorKernel := by
  have : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun reading latent => gaussianPDF ((4/5)*reading) (4/5) latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => gaussianPDF_ne_top)
  rw [actual_generative_joint_has_the_prior_times_likelihood_product_density,
    actual_swap_of_product_volume_with_density _ (by dsimp [sourceLikelihood];fun_prop),
    actual_posterior_kernel_has_the_true_gaussian_density,
    gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop),Measure.compProd_const]
  apply congrArg (fun density => (volume.prod volume).withDensity density)
  funext pair
  exact actual_extended_density_bayes_factorization pair.2 pair.1

theorem actual_source_reading_three_has_the_same_derived_posterior_kernel :
    posteriorKernel 3=sourcePosterior 3 := by
  rw [actual_normalized_bayes_posterior_is_the_derived_gaussian_for_every_reading]
  rfl

end SafeLearning.CompleteAppliedGaussianPosteriorJoint
