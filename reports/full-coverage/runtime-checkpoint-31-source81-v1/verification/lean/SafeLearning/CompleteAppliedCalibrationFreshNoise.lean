import SafeLearning.CompleteAppliedCalibrationPrediction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedCalibrationFreshNoise
open CompleteAppliedSequentialCalibrationJoint CompleteAppliedCalibrationPrediction

def posteriorWithFreshNoise (noiseLaw : Measure ℝ) : Kernel (ℝ×ℝ) (ℝ×ℝ) :=
  offsetPosteriorKernel.prod (Kernel.const (ℝ×ℝ) noiseLaw)

instance posteriorWithFreshNoise_markov (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    IsMarkovKernel (posteriorWithFreshNoise noiseLaw) := by
  unfold posteriorWithFreshNoise;infer_instance

theorem actual_independent_fresh_noise_preserves_the_derived_calibration_disintegration
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    (calibrationJoint.prod noiseLaw).map
      (fun pair:(ℝ×(ℝ×ℝ))×ℝ=>(pair.1.2,(pair.1.1,pair.2)))=
        readingPairLaw ⊗ₘ posteriorWithFreshNoise noiseLaw := by
  have hp := Measure.map_prod_map calibrationJoint noiseLaw measurable_swap measurable_id
  simp only [Measure.map_id] at hp
  have heq : ((calibrationJoint.prod noiseLaw).map
      (fun pair:(ℝ×(ℝ×ℝ))×ℝ=>(pair.1.2,(pair.1.1,pair.2))))=
      (((calibrationJoint.map Prod.swap).prod noiseLaw).map MeasurableEquiv.prodAssoc) := by
    rw [hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [heq,actual_two_reading_generative_joint_has_the_derived_conditional_offset_kernel]
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻a,(test ∘ MeasurableEquiv.prodAssoc) a
    ∂(readingPairLaw ⊗ₘ offsetPosteriorKernel).prod noiseLaw)=_
  rw [lintegral_prod _ (by fun_prop),
    Measure.lintegral_compProd ((htest.comp MeasurableEquiv.prodAssoc.measurable).lintegral_prod_right'),
    Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro readings
  rw [posteriorWithFreshNoise,Kernel.prod_apply,Kernel.const_apply,
    lintegral_prod _ (by fun_prop)]
  rfl

theorem actual_observed_calibration_leaves_fresh_noise_independent_of_the_offset
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] :
    posteriorWithFreshNoise noiseLaw (2,-1)=(gaussianReal (7/6) (2/3)).prod noiseLaw ∧
      IndepFun (fun pair:ℝ×ℝ=>pair.1-7/6) Prod.snd
        (posteriorWithFreshNoise noiseLaw (2,-1)) := by
  have heq : posteriorWithFreshNoise noiseLaw (2,-1)=
      (gaussianReal (7/6) (2/3)).prod noiseLaw := by
    rw [posteriorWithFreshNoise,Kernel.prod_apply,Kernel.const_apply,
      actual_observed_readings_have_the_literal_conditional_gaussian]
  refine ⟨heq,?_⟩
  rw [heq]
  exact indepFun_prod (show Measurable (fun offset:ℝ=>offset-7/6) by fun_prop) measurable_id

theorem actual_observed_calibration_and_fresh_standard_noise_have_the_true_predictive_law :
    HasLaw (fun pair:ℝ×ℝ=>pair.1-7/6+pair.2) (gaussianReal 0 (5/3))
      (posteriorWithFreshNoise (gaussianReal 0 1) (2,-1)) := by
  have he := actual_observed_calibration_leaves_fresh_noise_independent_of_the_offset
    (gaussianReal 0 1)
  have hfirst : HasLaw Prod.fst (gaussianReal (7/6) (2/3))
      ((gaussianReal (7/6) (2/3)).prod (gaussianReal 0 1)) := by
    refine ⟨measurable_fst.aemeasurable,?_⟩
    simp
  have hsecond : HasLaw Prod.snd (gaussianReal 0 1)
      ((gaussianReal (7/6) (2/3)).prod (gaussianReal 0 1)) := by
    refine ⟨measurable_snd.aemeasurable,?_⟩
    simp
  have hoffset := gaussianReal_sub_const hfirst (7/6)
  norm_num at hoffset
  rw [←he.1] at hoffset hsecond
  exact (actual_posterior_offset_and_independent_fresh_noise_give_the_predictive_gaussian
    hoffset hsecond he.2).1

theorem actual_fresh_reading_two_millimetre_probability_is_the_rounded_predictive_value :
    |(posteriorWithFreshNoise (gaussianReal 0 1) (2,-1)).real
        {pair:ℝ×ℝ | |pair.1-7/6+pair.2|≤2}-(87866/100000:ℝ)|<1/200000 ∧
      (posteriorWithFreshNoise (gaussianReal 0 1) (2,-1)).real
        {pair:ℝ×ℝ | |pair.1-7/6+pair.2|≤2}<(98/100:ℝ) := by
  rw [actual_zero_mean_gaussian_two_millimetre_probability (5/3) (by norm_num)
    actual_observed_calibration_and_fresh_standard_noise_have_the_true_predictive_law]
  exact actual_offset_and_predictive_two_millimetre_probability_roundings_and_requirement.2.2

end SafeLearning.CompleteAppliedCalibrationFreshNoise
