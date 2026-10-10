import SafeLearning.CompleteAppliedSequentialCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedSequentialCalibrationJoint
open CompleteAppliedSequentialCalibration CompleteAppliedGaussianBayesJoint

def readingPairKernel : Kernel ℝ (ℝ×ℝ) :=
  (observationKernel 1).prod (observationKernel 4)
def conditionalSecondReading : Kernel ℝ ℝ :=
  ⟨fun first=>gaussianReal (4*first/5) (24/5),by fun_prop⟩
def readingPairLaw : Measure (ℝ×ℝ) := gaussianReal 0 5 ⊗ₘ conditionalSecondReading
def offsetPosteriorKernel : Kernel (ℝ×ℝ) ℝ :=
  ⟨fun readings=>gaussianReal (calibratedMean readings.1 readings.2) (2/3),
    by dsimp [calibratedMean];fun_prop⟩
def calibrationJoint : Measure (ℝ×(ℝ×ℝ)) := gaussianReal 0 4 ⊗ₘ readingPairKernel

instance readingPairKernel_markov : IsMarkovKernel readingPairKernel := by
  unfold readingPairKernel;infer_instance
instance conditionalSecondReading_markov : IsMarkovKernel conditionalSecondReading :=
  ⟨fun _=>by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩
instance offsetPosteriorKernel_markov : IsMarkovKernel offsetPosteriorKernel :=
  ⟨fun _=>by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩
instance readingPairLaw_probability : IsProbabilityMeasure readingPairLaw := by
  unfold readingPairLaw;infer_instance
instance calibrationJoint_probability : IsProbabilityMeasure calibrationJoint := by
  unfold calibrationJoint;infer_instance

theorem actual_conditionally_independent_reading_kernel_has_the_two_likelihood_density :
    readingPairKernel=(Kernel.const ℝ (volume.prod volume)).withDensity
      (fun latent readings=>readingsLikelihood readings.1 readings.2 latent) := by
  ext latent event hevent
  rw [Kernel.withDensity_apply' _ (by unfold readingsLikelihood;fun_prop),Kernel.const_apply]
  rw [readingPairKernel,Kernel.prod_apply]
  change ((gaussianReal latent 1).prod (gaussianReal latent 4)) event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),gaussianReal_of_var_ne_zero _ (by norm_num),
    prod_withDensity (by fun_prop) (by fun_prop),withDensity_apply _ hevent]
  rfl

theorem actual_full_calibration_joint_has_the_true_prior_and_two_likelihood_density :
    calibrationJoint=(volume.prod (volume.prod volume)).withDensity
      (fun pair=>gaussianPDF 0 4 pair.1*readingsLikelihood pair.2.1 pair.2.2 pair.1) := by
  have : IsSFiniteKernel ((Kernel.const ℝ (volume.prod volume)).withDensity
      (fun latent readings=>readingsLikelihood readings.1 readings.2 latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>by
      unfold readingsLikelihood;exact ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top)
  rw [calibrationJoint,actual_conditionally_independent_reading_kernel_has_the_two_likelihood_density,
    gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by unfold readingsLikelihood;fun_prop),
    Measure.compProd_const]

theorem actual_reading_pair_law_has_the_derived_evidence_density :
    readingPairLaw=(volume.prod volume).withDensity
      (fun readings=>readingsEvidence readings.1 readings.2) := by
  have hkernel : conditionalSecondReading=(Kernel.const ℝ volume).withDensity
      (fun first second=>gaussianPDF (4*first/5) (24/5) second) := by
    ext first event hevent
    rw [Kernel.withDensity_apply' _ (by fun_prop),Kernel.const_apply]
    change gaussianReal (4*first/5) (24/5) event=_
    rw [gaussianReal_of_var_ne_zero _ (by norm_num),withDensity_apply _ hevent]
  have : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun first second=>gaussianPDF (4*first/5) (24/5) second)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>gaussianPDF_ne_top)
  rw [readingPairLaw,hkernel,gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop),Measure.compProd_const]
  rfl

theorem actual_offset_posterior_kernel_has_the_derived_density :
    offsetPosteriorKernel=(Kernel.const (ℝ×ℝ) volume).withDensity
      (fun readings latent=>gaussianPDF (calibratedMean readings.1 readings.2) (2/3) latent) := by
  ext readings event hevent
  rw [Kernel.withDensity_apply' _ (by dsimp [calibratedMean];fun_prop),Kernel.const_apply]
  change gaussianReal (calibratedMean readings.1 readings.2) (2/3) event=_
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),withDensity_apply _ hevent]

theorem actual_swap_of_the_triple_product_density
    (density : ℝ×(ℝ×ℝ)→ℝ≥0∞) (hd : Measurable density) :
    ((volume.prod (volume.prod volume)).withDensity density).map Prod.swap=
      ((volume.prod volume).prod volume).withDensity (fun pair=>density pair.swap) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_swap]
  change (∫⁻a,(test ∘ Prod.swap) a ∂(volume.prod (volume.prod volume)).withDensity density)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (htest.comp measurable_swap)]
  change _=(∫⁻a,test a ∂((volume.prod volume).prod volume).withDensity (density ∘ Prod.swap))
  rw [lintegral_withDensity_eq_lintegral_mul _ (hd.comp measurable_swap) htest]
  have ht : Measurable (fun pair:(ℝ×ℝ)×ℝ=>density pair.swap*test pair) :=
    (hd.comp measurable_swap).mul htest
  have h := lintegral_map ht measurable_swap (μ:=volume.prod (volume.prod volume))
  rw [Measure.prod_swap] at h
  simpa only [Prod.swap_swap,Function.comp_def,Pi.mul_apply] using h.symm

theorem actual_two_reading_generative_joint_has_the_derived_conditional_offset_kernel :
    calibrationJoint.map Prod.swap=readingPairLaw ⊗ₘ offsetPosteriorKernel := by
  have : IsSFiniteKernel ((Kernel.const (ℝ×ℝ) volume).withDensity
      (fun readings latent=>gaussianPDF (calibratedMean readings.1 readings.2) (2/3) latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _=>gaussianPDF_ne_top)
  rw [actual_full_calibration_joint_has_the_true_prior_and_two_likelihood_density,
    actual_swap_of_the_triple_product_density _ (by unfold readingsLikelihood;fun_prop),
    actual_reading_pair_law_has_the_derived_evidence_density,
    actual_offset_posterior_kernel_has_the_derived_density,
    Measure.withDensity_compProd_withDensity (by unfold readingsEvidence;fun_prop)
      (by dsimp [calibratedMean];fun_prop),Measure.compProd_const]
  apply congrArg (fun density=>((volume.prod volume).prod volume).withDensity density)
  funext pair
  exact actual_independent_two_likelihood_product_has_the_derived_bayes_factorization _ _ _

theorem actual_observed_readings_have_the_literal_conditional_gaussian :
    offsetPosteriorKernel (2,-1)=gaussianReal (7/6) (2/3) := by
  change gaussianReal (calibratedMean 2 (-1)) (2/3)=_
  norm_num [calibratedMean]

end SafeLearning.CompleteAppliedSequentialCalibrationJoint
