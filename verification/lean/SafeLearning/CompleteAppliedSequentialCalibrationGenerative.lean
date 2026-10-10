import SafeLearning.CompleteAppliedSequentialCalibrationJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedSequentialCalibrationGenerative
open CompleteAppliedSequentialCalibrationJoint

def generateReadings (pair : ℝ×(ℝ×ℝ)) : ℝ×(ℝ×ℝ) :=
  (pair.1,(pair.1+pair.2.1,pair.1+pair.2.2))

theorem actual_independent_prior_and_two_noises_construct_the_calibration_joint :
    ((gaussianReal 0 4).prod ((gaussianReal 0 1).prod (gaussianReal 0 4))).map
      generateReadings=calibrationJoint := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by unfold generateReadings;fun_prop)]
  change (∫⁻pair,(test ∘ generateReadings) pair
    ∂(gaussianReal 0 4).prod ((gaussianReal 0 1).prod (gaussianReal 0 4)))=_
  rw [lintegral_prod _ (by unfold generateReadings;fun_prop),calibrationJoint,
    Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro latent
  have hm : ((gaussianReal 0 1).prod (gaussianReal 0 4)).map
      (fun noises:ℝ×ℝ=>(latent+noises.1,latent+noises.2))=
        (gaussianReal latent 1).prod (gaussianReal latent 4) := by
    have h := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 4)
      (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
      (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
    rw [gaussianReal_map_const_add,gaussianReal_map_const_add] at h
    simp only [zero_add] at h
    convert h.symm using 1
    ext pair
    rfl
  have ht : Measurable (fun readings:ℝ×ℝ=>test (latent,readings)) :=
    htest.comp measurable_prodMk_left
  have hi := lintegral_map ht (show Measurable (fun noises:ℝ×ℝ=>(latent+noises.1,latent+noises.2)) by fun_prop)
    (μ:=(gaussianReal 0 1).prod (gaussianReal 0 4))
  rw [hm] at hi
  rw [readingPairKernel,Kernel.prod_apply]
  change (∫⁻noises,test (latent,(latent+noises.1,latent+noises.2))
    ∂(gaussianReal 0 1).prod (gaussianReal 0 4))=
      (∫⁻readings,test (latent,readings) ∂(gaussianReal latent 1).prod (gaussianReal latent 4))
  exact hi.symm

theorem actual_arbitrary_mutually_independent_measurement_model_has_the_joint_disintegration
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Fin 3→Ω→ℝ) (hX : ∀i,AEMeasurable (X i) P) (hindep : iIndepFun X P)
    (hprior : HasLaw (X 0) (gaussianReal 0 4) P)
    (hfirst : HasLaw (X 1) (gaussianReal 0 1) P)
    (hsecond : HasLaw (X 2) (gaussianReal 0 4) P) :
    HasLaw (fun omega=>(X 0 omega,(X 0 omega+X 1 omega,X 0 omega+X 2 omega)))
      calibrationJoint P ∧
    HasLaw (fun omega=>((X 0 omega+X 1 omega,X 0 omega+X 2 omega),X 0 omega))
      (readingPairLaw ⊗ₘ offsetPosteriorKernel) P := by
  have hnoise := (hindep.indepFun (show (1:Fin 3)≠2 by decide)).hasLaw_prod hfirst hsecond
  have hpair := (hindep.indepFun_prodMk₀ hX 1 2 0 (by decide) (by decide)).symm.hasLaw_prod
    hprior hnoise
  have hg : HasLaw generateReadings calibrationJoint
      ((gaussianReal 0 4).prod ((gaussianReal 0 1).prod (gaussianReal 0 4))) :=
    ⟨(show Measurable generateReadings by unfold generateReadings;fun_prop).aemeasurable,
      actual_independent_prior_and_two_noises_construct_the_calibration_joint⟩
  have hj := hg.comp hpair
  have hswap : HasLaw Prod.swap (readingPairLaw ⊗ₘ offsetPosteriorKernel) calibrationJoint :=
    ⟨measurable_swap.aemeasurable,
      actual_two_reading_generative_joint_has_the_derived_conditional_offset_kernel⟩
  exact ⟨hj,hswap.comp hj⟩

theorem actual_unconditional_calibration_readings_share_offset_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Fin 3→Ω→ℝ) (hindep : iIndepFun X P)
    (hprior : HasLaw (X 0) (gaussianReal 0 4) P)
    (hfirst : HasLaw (X 1) (gaussianReal 0 1) P)
    (hsecond : HasLaw (X 2) (gaussianReal 0 4) P) :
    covariance (fun omega=>X 0 omega+X 1 omega)
      (fun omega=>X 0 omega+X 2 omega) P=4 := by
  have h0 := hprior.memLp (memLp_id_gaussianReal 2)
  have h1 := hfirst.memLp (memLp_id_gaussianReal 2)
  have h2 := hsecond.memLp (memLp_id_gaussianReal 2)
  have hc01 := (hindep.indepFun (show (0:Fin 3)≠1 by decide)).covariance_eq_zero h0 h1
  have hc02 := (hindep.indepFun (show (0:Fin 3)≠2 by decide)).covariance_eq_zero h0 h2
  have hc12 := (hindep.indepFun (show (1:Fin 3)≠2 by decide)).covariance_eq_zero h1 h2
  change covariance (X 0+X 1) (X 0+X 2) P=_
  rw [covariance_add_left h0 h1 (h0.add h2),covariance_add_right h0 h0 h2,
    covariance_add_right h1 h0 h2,covariance_self h0.aemeasurable,
    hprior.variance_eq,variance_id_gaussianReal,hc02,hc12,covariance_comm (X 1) (X 0),hc01]
  norm_num

end SafeLearning.CompleteAppliedSequentialCalibrationGenerative
