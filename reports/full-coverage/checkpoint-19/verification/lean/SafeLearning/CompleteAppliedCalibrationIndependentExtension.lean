import SafeLearning.CompleteAppliedSequentialCalibrationJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedCalibrationIndependentExtension
open CompleteAppliedSequentialCalibrationJoint

def extendedPosteriorKernel {E : Type*} [MeasurableSpace E] (independentLaw : Measure E) :
    Kernel (ℝ×ℝ) (ℝ×E) := offsetPosteriorKernel.prod (Kernel.const (ℝ×ℝ) independentLaw)

instance extendedPosteriorKernel_markov {E : Type*} [MeasurableSpace E]
    (independentLaw : Measure E) [IsProbabilityMeasure independentLaw] :
    IsMarkovKernel (extendedPosteriorKernel independentLaw) := by
  unfold extendedPosteriorKernel;infer_instance

theorem actual_independent_data_preserves_the_derived_calibration_disintegration
    {E : Type*} [MeasurableSpace E] (independentLaw : Measure E)
    [IsProbabilityMeasure independentLaw] :
    (calibrationJoint.prod independentLaw).map
      (fun pair:(ℝ×(ℝ×ℝ))×E=>(pair.1.2,(pair.1.1,pair.2)))=
        readingPairLaw ⊗ₘ extendedPosteriorKernel independentLaw := by
  have hp := Measure.map_prod_map calibrationJoint independentLaw measurable_swap measurable_id
  simp only [Measure.map_id] at hp
  have heq : ((calibrationJoint.prod independentLaw).map
      (fun pair:(ℝ×(ℝ×ℝ))×E=>(pair.1.2,(pair.1.1,pair.2))))=
      (((calibrationJoint.map Prod.swap).prod independentLaw).map MeasurableEquiv.prodAssoc) := by
    rw [hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [heq,actual_two_reading_generative_joint_has_the_derived_conditional_offset_kernel]
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻a,(test ∘ MeasurableEquiv.prodAssoc) a
    ∂(readingPairLaw ⊗ₘ offsetPosteriorKernel).prod independentLaw)=_
  rw [lintegral_prod _ (by fun_prop),
    Measure.lintegral_compProd ((htest.comp MeasurableEquiv.prodAssoc.measurable).lintegral_prod_right'),
    Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro readings
  rw [extendedPosteriorKernel,Kernel.prod_apply,Kernel.const_apply,
    lintegral_prod _ (by fun_prop)]
  rfl

theorem actual_observed_calibration_preserves_the_entire_independent_data_law
    {E : Type*} [MeasurableSpace E] (independentLaw : Measure E)
    [IsProbabilityMeasure independentLaw] :
    extendedPosteriorKernel independentLaw (2,-1)=
      (gaussianReal (7/6) (2/3)).prod independentLaw := by
  rw [extendedPosteriorKernel,Kernel.prod_apply,Kernel.const_apply,
    actual_observed_readings_have_the_literal_conditional_gaussian]

end SafeLearning.CompleteAppliedCalibrationIndependentExtension
