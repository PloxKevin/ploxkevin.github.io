import SafeLearning.CompleteModulesGPCorrelatedPrior
import SafeLearning.CompleteModulesGPCorrelatedPosterior

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteModulesGPCorrelatedConsequences
open CompleteModulesGPCorrelatedPrior CompleteModulesGPCorrelatedPosterior

def sourceNoiseLaw : Measure ℝ := gaussianReal 0 (1/4)
def rawLaw : Measure ((ℝ × ℝ) × ℝ) := baseLaw.prod sourceNoiseLaw
def sourceGenerativeMap (triple : (ℝ × ℝ) × ℝ) : ℝ × (ℝ × ℝ) :=
  (triple.1.1+triple.2,sourceLatentPair triple.1)
def sourceGenerativeJoint : Measure (ℝ × (ℝ × ℝ)) := rawLaw.map sourceGenerativeMap
instance sourceNoiseLaw_probability : IsProbabilityMeasure sourceNoiseLaw := by
  unfold sourceNoiseLaw;infer_instance
instance rawLaw_probability : IsProbabilityMeasure rawLaw := by unfold rawLaw;infer_instance

lemma actual_prior_pair_and_measurement_noise_are_independent_in_the_source_model :
    IndepFun (fun triple : (ℝ × ℝ) × ℝ => sourceLatentPair triple.1) Prod.snd rawLaw := by
  unfold rawLaw
  exact indepFun_prod (by unfold sourceLatentPair;fun_prop) measurable_id

lemma actual_source_model_latent_pair_has_the_true_correlated_prior_law :
    HasLaw (fun triple : (ℝ × ℝ) × ℝ => sourceLatentPair triple.1) sourcePriorLaw rawLaw := by
  refine ⟨by unfold sourceLatentPair;fun_prop,?_⟩
  rw [rawLaw,← Measure.map_map (by unfold sourceLatentPair;fun_prop) measurable_fst,
    Measure.map_fst_prod,measure_univ,one_smul]
  rfl

lemma actual_source_model_measurement_noise_has_the_true_gaussian_law :
    HasLaw Prod.snd sourceNoiseLaw rawLaw :=
  ⟨measurable_snd.aemeasurable,by simp [rawLaw]⟩

theorem actual_source_correlated_prior_with_independent_noise_constructs_the_joint :
    sourceGenerativeJoint = sourceJoint := by
  have hj := CompleteAppliedGaussianBayesJoint.actual_independent_prior_noise_pair_constructs_the_same_joint
    0 1 (1/4)
  have hm : Measurable sourceGenerativeMap := by unfold sourceGenerativeMap sourceLatentPair;fun_prop
  have hg : Measurable (fun pair : ℝ × ℝ => (pair.1,pair.1+pair.2)) := by fun_prop
  have hs : Measurable (fun triple : (ℝ × ℝ) × ℝ =>
      (triple.1.1, latentPair (triple.1.2,triple.2))) := by unfold latentPair;fun_prop
  rw [sourceJoint,← hj,Measure.map_map measurable_swap hg]
  have he : (((gaussianReal 0 1).prod (gaussianReal 0 (1/4))).map
      (Prod.swap ∘ fun pair : ℝ × ℝ => (pair.1,pair.1+pair.2))).prod residualLaw =
      (((gaussianReal 0 1).prod (gaussianReal 0 (1/4))).prod residualLaw).map
        (Prod.map (Prod.swap ∘ fun pair : ℝ × ℝ => (pair.1,pair.1+pair.2)) id) := by
    simpa using Measure.map_prod_map
      ((gaussianReal 0 1).prod (gaussianReal 0 (1/4))) residualLaw
      (show Measurable (Prod.swap ∘ fun pair : ℝ × ℝ => (pair.1,pair.1+pair.2)) by fun_prop) measurable_id
  rw [he,Measure.map_map hs (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro test htest
  have hleft : Measurable (fun triple : (ℝ × ℝ) × ℝ => test (sourceGenerativeMap triple)) := htest.comp hm
  have hright : Measurable (fun triple : (ℝ × ℝ) × ℝ =>
      test (triple.1.1+triple.1.2,latentPair (triple.1.1,triple.2))) := by
    exact htest.comp (by unfold latentPair;fun_prop)
  change (∫⁻ triple,test (sourceGenerativeMap triple) ∂rawLaw)=_
  rw [rawLaw,baseLaw,lintegral_prod _ hleft.aemeasurable,
    lintegral_prod _ hleft.lintegral_prod_right.aemeasurable,
    lintegral_map htest (by fun_prop),lintegral_prod _ hright.aemeasurable,
    lintegral_prod _ hright.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro latent
  change (∫⁻ z,∫⁻ noise,test (latent+noise,sourceLatentPair (latent,z)) ∂sourceNoiseLaw
    ∂gaussianReal 0 (3/4))=
    ∫⁻ noise,∫⁻ z,test (latent+noise,latentPair (latent,z)) ∂residualLaw ∂gaussianReal 0 (1/4)
  unfold sourceNoiseLaw residualLaw
  change (∫⁻ z,∫⁻ noise,test (latent+noise,sourceLatentPair (latent,z)) ∂gaussianReal 0 (1/4)
    ∂gaussianReal 0 (3/4))=
    ∫⁻ noise,∫⁻ z,test (latent+noise,sourceLatentPair (latent,z)) ∂gaussianReal 0 (3/4) ∂gaussianReal 0 (1/4)
  exact lintegral_lintegral_swap (by fun_prop)

theorem actual_source_generative_model_has_the_derived_correlated_posterior_disintegration :
    sourceGenerativeJoint = sourceDataLaw ⊗ₘ posteriorPairKernel :=
  actual_source_correlated_prior_with_independent_noise_constructs_the_joint.trans
    actual_source_correlated_latent_joint_has_the_derived_conditional_pair_kernel

lemma actual_independent_fresh_noise_adds_its_variance_to_a_gaussian_latent_law
    (mean : ℝ) (variance : ℝ≥0) :
    ((gaussianReal mean variance).prod sourceNoiseLaw).map
      (fun pair : ℝ × ℝ => pair.1+pair.2) = gaussianReal mean (variance+1/4) := by
  have ha : HasLaw Prod.fst (gaussianReal mean variance)
      ((gaussianReal mean variance).prod sourceNoiseLaw) := ⟨by fun_prop,by simp⟩
  have hn : HasLaw Prod.snd sourceNoiseLaw
      ((gaussianReal mean variance).prod sourceNoiseLaw) := ⟨by fun_prop,by simp⟩
  have hi : IndepFun Prod.fst Prod.snd ((gaussianReal mean variance).prod sourceNoiseLaw) :=
    indepFun_prod measurable_id measurable_id
  simpa [sourceNoiseLaw] using gaussianReal_add_gaussianReal_of_indepFun hi ha hn

theorem actual_reading_two_fresh_observations_have_the_printed_latent_variance_plus_noise :
    (((posteriorPairKernel 2).map Prod.fst).prod sourceNoiseLaw).map
        (fun pair : ℝ × ℝ => pair.1+pair.2) = gaussianReal (8/5) (9/20) ∧
    (((posteriorPairKernel 2).map Prod.snd).prod sourceNoiseLaw).map
        (fun pair : ℝ × ℝ => pair.1+pair.2) = gaussianReal (4/5) (21/20) := by
  rw [actual_source_reading_two_has_the_printed_latent_posterior_laws.1,
    actual_source_reading_two_has_the_printed_latent_posterior_laws.2]
  constructor
  · have h := actual_independent_fresh_noise_adds_its_variance_to_a_gaussian_latent_law (8/5) (1/5)
    norm_num at h ⊢
    exact h
  · have h := actual_independent_fresh_noise_adds_its_variance_to_a_gaussian_latent_law (4/5) (4/5)
    norm_num at h ⊢
    exact h

theorem actual_source_latent_uncertainty_and_less_correlated_variance_reduction :
    (0:ℝ)<1/5 ∧ 1/5<4/5 ∧ 4/5<1 ∧ (9/20:ℝ)=1/5+1/4 ∧
      (21/20:ℝ)=4/5+1/4 := by norm_num

end SafeLearning.CompleteModulesGPCorrelatedConsequences
