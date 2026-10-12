import SafeLearning.CompleteAppliedGaussianFourUpdate
import SafeLearning.CompleteAppliedGaussianBayesJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianFourJoint
open CompleteAppliedGaussianFourUpdate CompleteAppliedGaussianBayesJoint

def volumeFour : Measure Readings := volume.prod (volume.prod (volume.prod volume))
def readingKernel : Kernel ℝ Readings :=
  (observationKernel (1/4)).prod ((observationKernel (1/4)).prod
    ((observationKernel (1/4)).prod (observationKernel (1/4))))
def dataLaw : Measure Readings := volumeFour.withDensity readingsEvidence
def fullPosteriorKernel : Kernel Readings ℝ :=
  ⟨fun y=>gaussianReal (fourthMean y) (1/17),by dsimp [fourthMean];fun_prop⟩
def fullJoint : Measure (ℝ×Readings) := gaussianReal 0 1 ⊗ₘ readingKernel

instance volumeFour_sfinite : SFinite volumeFour := by unfold volumeFour;infer_instance
instance readingKernel_markov : IsMarkovKernel readingKernel := by
  unfold readingKernel;infer_instance
instance dataLaw_sfinite : SFinite dataLaw := by unfold dataLaw;infer_instance
instance fullPosteriorKernel_markov : IsMarkovKernel fullPosteriorKernel :=
  ⟨fun _=>by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩
instance fullJoint_probability : IsProbabilityMeasure fullJoint := by
  unfold fullJoint;infer_instance

theorem actual_four_conditionally_independent_readings_have_the_full_product_density :
    readingKernel=(Kernel.const ℝ volumeFour).withDensity
      (fun latent y=>readingsLikelihood y latent) := by
  ext latent event hevent
  rw [Kernel.withDensity_apply' _ (by unfold readingsLikelihood;fun_prop),Kernel.const_apply]
  simp only [readingKernel,Kernel.prod_apply]
  change ((gaussianReal latent (1/4)).prod ((gaussianReal latent (1/4)).prod
    ((gaussianReal latent (1/4)).prod (gaussianReal latent (1/4))))) event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop)]
  change (volumeFour.withDensity (fun y=>gaussianPDF latent (1/4) y.1*
    (gaussianPDF latent (1/4) y.2.1*(gaussianPDF latent (1/4) y.2.2.1*
      gaussianPDF latent (1/4) y.2.2.2)))) event=_
  have he : (fun y:Readings=>gaussianPDF latent (1/4) y.1*
    (gaussianPDF latent (1/4) y.2.1*(gaussianPDF latent (1/4) y.2.2.1*
      gaussianPDF latent (1/4) y.2.2.2)))=fun y=>readingsLikelihood y latent := by
    funext y;unfold readingsLikelihood;ring
  rw [he,withDensity_apply _ hevent]

theorem actual_full_prior_and_four_readings_have_the_true_joint_density :
    fullJoint=(volume.prod volumeFour).withDensity
      (fun pair=>gaussianPDF 0 1 pair.1*readingsLikelihood pair.2 pair.1) := by
  have : IsSFiniteKernel ((Kernel.const ℝ volumeFour).withDensity
      (fun latent y=>readingsLikelihood y latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>by
      unfold readingsLikelihood
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top) gaussianPDF_ne_top)
          gaussianPDF_ne_top)
  rw [fullJoint,actual_four_conditionally_independent_readings_have_the_full_product_density,
    gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by unfold readingsLikelihood;fun_prop),
    Measure.compProd_const]

theorem actual_swap_of_four_reading_product_density
    (density : ℝ×Readings→ℝ≥0∞) (hd : Measurable density) :
    ((volume.prod volumeFour).withDensity density).map Prod.swap=
      (volumeFour.prod volume).withDensity (fun pair=>density pair.swap) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_swap]
  change (∫⁻a,(test ∘ Prod.swap) a ∂(volume.prod volumeFour).withDensity density)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (htest.comp measurable_swap)]
  change _=(∫⁻a,test a ∂(volumeFour.prod volume).withDensity (density ∘ Prod.swap))
  rw [lintegral_withDensity_eq_lintegral_mul _ (hd.comp measurable_swap) htest]
  have ht : Measurable (fun pair:Readings×ℝ=>density pair.swap*test pair) :=
    (hd.comp measurable_swap).mul htest
  have h:=lintegral_map ht measurable_swap (μ:=volume.prod volumeFour)
  rw [Measure.prod_swap] at h
  simpa only [Prod.swap_swap,Function.comp_def,Pi.mul_apply] using h.symm

theorem actual_full_posterior_kernel_has_the_derived_density :
    fullPosteriorKernel=(Kernel.const Readings volume).withDensity
      (fun y latent=>gaussianPDF (fourthMean y) (1/17) latent) := by
  ext y event hevent
  rw [Kernel.withDensity_apply' _ (by dsimp [fourthMean];fun_prop),Kernel.const_apply]
  change gaussianReal (fourthMean y) (1/17) event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),withDensity_apply _ hevent]

theorem actual_reversed_full_generative_joint_derives_the_four_data_conditional_kernel :
    fullJoint.map Prod.swap=dataLaw ⊗ₘ fullPosteriorKernel := by
  have : IsSFiniteKernel ((Kernel.const Readings volume).withDensity
      (fun y latent=>gaussianPDF (fourthMean y) (1/17) latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>gaussianPDF_ne_top)
  rw [actual_full_prior_and_four_readings_have_the_true_joint_density,
    actual_swap_of_four_reading_product_density _ (by unfold readingsLikelihood;fun_prop),
    dataLaw,actual_full_posterior_kernel_has_the_derived_density,
    Measure.withDensity_compProd_withDensity (by unfold readingsEvidence firstMean secondMean thirdMean;fun_prop)
      (by dsimp [fourthMean];fun_prop),Measure.compProd_const]
  apply congrArg (fun density=>(volumeFour.prod volume).withDensity density)
  funext pair
  exact actual_full_four_measurement_likelihood_has_the_derived_bayes_factorization _ _

theorem actual_data_law_is_the_genuine_marginal_of_the_constructed_joint :
    (fullJoint.map Prod.swap).fst=dataLaw := by
  rw [actual_reversed_full_generative_joint_derives_the_four_data_conditional_kernel,
    Measure.fst_compProd]

instance dataLaw_probability : IsProbabilityMeasure dataLaw := by
  rw [←actual_data_law_is_the_genuine_marginal_of_the_constructed_joint]
  infer_instance

theorem actual_average_nine_tenths_selects_the_derived_four_data_gaussian_kernel
    (y : Readings) (hy : readingAverage y=9/10) :
    fullPosteriorKernel y=gaussianReal (72/85) (1/17) := by
  change gaussianReal (fourthMean y) (1/17)=_
  have hm : fourthMean y=72/85 := by unfold readingAverage at hy;unfold fourthMean;linarith
  rw [hm]

end SafeLearning.CompleteAppliedGaussianFourJoint
