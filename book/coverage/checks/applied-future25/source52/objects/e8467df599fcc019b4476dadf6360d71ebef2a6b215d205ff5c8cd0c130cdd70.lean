import SafeLearning.CompleteAppliedSequentialCalibrationGenerative
import SafeLearning.CompleteAppliedCalibrationIndependentExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedCalibrationModelAssembly
open CompleteAppliedSequentialCalibrationJoint
open CompleteAppliedSequentialCalibrationGenerative
open CompleteAppliedCalibrationIndependentExtension

theorem actual_independent_fresh_data_has_the_derived_reading_and_offset_joint_law
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (independentLaw : Measure E) [IsProbabilityMeasure independentLaw]
    (model : Ω→ℝ×(ℝ×ℝ)) (fresh : Ω→E)
    (hmodel : HasLaw model calibrationJoint P) (hfresh : HasLaw fresh independentLaw P)
    (hindep : IndepFun model fresh P) :
    HasLaw (fun omega=>( (model omega).2,((model omega).1,fresh omega)))
      (readingPairLaw ⊗ₘ extendedPosteriorKernel independentLaw) P := by
  have hpair := hindep.hasLaw_prod hmodel hfresh
  have htransform : HasLaw (fun pair:(ℝ×(ℝ×ℝ))×E=>(pair.1.2,(pair.1.1,pair.2)))
      (readingPairLaw ⊗ₘ extendedPosteriorKernel independentLaw)
      (calibrationJoint.prod independentLaw) :=
    ⟨(show Measurable (fun pair:(ℝ×(ℝ×ℝ))×E=>(pair.1.2,(pair.1.1,pair.2)))
      by fun_prop).aemeasurable,
      actual_independent_data_preserves_the_derived_calibration_disintegration independentLaw⟩
  exact htransform.comp hpair

theorem actual_full_prior_calibration_noise_and_fresh_data_construct_the_posterior_model
    {E : Type*} [MeasurableSpace E]
    (independentLaw : Measure E) [IsProbabilityMeasure independentLaw] :
    (((gaussianReal 0 4).prod ((gaussianReal 0 1).prod (gaussianReal 0 4))).prod
      independentLaw).map
      (fun pair:(ℝ×(ℝ×ℝ))×E=>
        ((pair.1.1+pair.1.2.1,pair.1.1+pair.1.2.2),(pair.1.1,pair.2)))=
      readingPairLaw ⊗ₘ extendedPosteriorKernel independentLaw := by
  have hg := Measure.map_prod_map
    ((gaussianReal 0 4).prod ((gaussianReal 0 1).prod (gaussianReal 0 4))) independentLaw
    (show Measurable generateReadings by unfold generateReadings;fun_prop) measurable_id
  rw [actual_independent_prior_and_two_noises_construct_the_calibration_joint,
    Measure.map_id] at hg
  rw [←actual_independent_data_preserves_the_derived_calibration_disintegration independentLaw,
    hg,Measure.map_map (by fun_prop) (by unfold generateReadings;fun_prop)]
  rfl

end SafeLearning.CompleteAppliedCalibrationModelAssembly
