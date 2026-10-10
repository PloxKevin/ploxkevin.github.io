import SafeLearning.CompleteAppliedGaussianBayesJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteModulesGPCorrelatedPosterior

def residualLaw : Measure ℝ := gaussianReal 0 (3/4)
def sourcePosterior : Kernel ℝ ℝ := CompleteAppliedGaussianBayesJoint.posteriorKernel 0 1 (1/4)
def latentPair (az : ℝ × ℝ) : ℝ × ℝ := (az.1, (1/2)*az.1+az.2)
def posteriorPairKernel : Kernel ℝ (ℝ × ℝ) :=
  (sourcePosterior.prod (Kernel.const ℝ residualLaw)).map latentPair
def sourceDataLaw : Measure ℝ := gaussianReal 0 (5/4)
def sourceJoint : Measure (ℝ × (ℝ × ℝ)) :=
  (((CompleteAppliedGaussianBayesJoint.actualJoint 0 1 (1/4)).map Prod.swap).prod residualLaw).map
    (fun triple : (ℝ × ℝ) × ℝ => (triple.1.1, latentPair (triple.1.2,triple.2)))
instance residualLaw_probability : IsProbabilityMeasure residualLaw := by unfold residualLaw;infer_instance
instance sourcePosterior_markov : IsMarkovKernel sourcePosterior := by unfold sourcePosterior;infer_instance

lemma actual_independent_residual_lift_of_a_conditional_joint
    (nu : Measure ℝ) [SFinite nu] (kappa : Kernel ℝ ℝ) [IsMarkovKernel kappa]
    (rho : Measure ℝ) [IsProbabilityMeasure rho] :
    ((nu ⊗ₘ kappa).prod rho).map
      (fun triple : (ℝ × ℝ) × ℝ => (triple.1.1, latentPair (triple.1.2,triple.2))) =
      nu ⊗ₘ ((kappa.prod (Kernel.const ℝ rho)).map latentPair) := by
  have hmap : Measurable (fun triple : (ℝ × ℝ) × ℝ =>
      (triple.1.1, latentPair (triple.1.2,triple.2))) := by unfold latentPair;fun_prop
  have hpair : Measurable latentPair := by unfold latentPair;fun_prop
  apply Measure.ext_of_lintegral
  intro test htest
  have hm : Measurable (fun triple : (ℝ × ℝ) × ℝ =>
      test (triple.1.1,latentPair (triple.1.2,triple.2))) := htest.comp hmap
  rw [lintegral_map htest hmap,lintegral_prod _ hm.aemeasurable,
    Measure.lintegral_compProd hm.lintegral_prod_right,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro reading
  have ht : Measurable (fun pair : ℝ × ℝ => test (reading,pair)) :=
    htest.comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (fun az : ℝ × ℝ => test (reading,latentPair az)) := ht.comp hpair
  rw [Kernel.map_apply _ hpair,lintegral_map ht hpair,
    Kernel.prod_apply,Kernel.const_apply,lintegral_prod _ hh.aemeasurable]

theorem actual_source_correlated_latent_joint_has_the_derived_conditional_pair_kernel :
    sourceJoint = sourceDataLaw ⊗ₘ posteriorPairKernel := by
  have h := CompleteAppliedGaussianBayesJoint.actual_reversed_generative_joint_is_the_true_evidence_and_derived_posterior_disintegration
    0 1 (1/4) (by norm_num) (by norm_num)
  norm_num at h
  rw [sourceJoint,h]
  exact actual_independent_residual_lift_of_a_conditional_joint _ _ _

theorem actual_source_first_latent_marginal_of_the_posterior_pair_is_the_true_gaussian
    (reading : ℝ) :
    (posteriorPairKernel reading).map Prod.fst =
      gaussianReal ((4/5)*reading) (1/5) := by
  rw [posteriorPairKernel,Kernel.map_apply _ (by unfold latentPair;fun_prop),
    Kernel.prod_apply,Kernel.const_apply,Measure.map_map measurable_fst (by unfold latentPair;fun_prop)]
  change ((sourcePosterior reading).prod residualLaw).map Prod.fst = _
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  change gaussianReal (CompleteAppliedGaussianBayesGeneral.posteriorMean 0 reading 1 (1/4))
      (CompleteAppliedGaussianBayesGeneral.posteriorVariance 1 (1/4)) = _
  congr 1
  · norm_num [CompleteAppliedGaussianBayesGeneral.posteriorMean];ring
  · norm_num [CompleteAppliedGaussianBayesGeneral.posteriorVariance]

theorem actual_source_second_latent_marginal_of_the_posterior_pair_is_the_true_gaussian
    (reading : ℝ) :
    (posteriorPairKernel reading).map Prod.snd =
      gaussianReal ((2/5)*reading) (4/5) := by
  rw [posteriorPairKernel,Kernel.map_apply _ (by unfold latentPair;fun_prop),
    Kernel.prod_apply,Kernel.const_apply,Measure.map_map measurable_snd (by unfold latentPair;fun_prop)]
  let mu : Measure ℝ := sourcePosterior reading
  haveI : IsProbabilityMeasure mu := by unfold mu;infer_instance
  have ha : HasLaw Prod.fst mu (mu.prod residualLaw) :=
    ⟨measurable_fst.aemeasurable,by simp⟩
  have hz : HasLaw Prod.snd residualLaw (mu.prod residualLaw) :=
    ⟨measurable_snd.aemeasurable,by simp⟩
  have haa : HasLaw Prod.fst
      (gaussianReal ((4/5)*reading) (1/5)) (mu.prod residualLaw) := by
    have he : mu = gaussianReal ((4/5)*reading) (1/5) := by
      unfold mu sourcePosterior
      change gaussianReal (CompleteAppliedGaussianBayesGeneral.posteriorMean 0 reading 1 (1/4))
        (CompleteAppliedGaussianBayesGeneral.posteriorVariance 1 (1/4)) = _
      congr 1
      · norm_num [CompleteAppliedGaussianBayesGeneral.posteriorMean];ring
      · norm_num [CompleteAppliedGaussianBayesGeneral.posteriorVariance]
    exact ⟨ha.aemeasurable,ha.map_eq.trans he⟩
  have hs := gaussianReal_const_mul haa (1/2)
  have hind : IndepFun (fun pair : ℝ × ℝ => (1/2)*pair.1) Prod.snd (mu.prod residualLaw) :=
    indepFun_prod (by fun_prop) measurable_id
  have hadd := gaussianReal_add_gaussianReal_of_indepFun hind hs hz
  change ((mu.prod residualLaw).map (fun pair : ℝ × ℝ => (1/2)*pair.1+pair.2)) = _
  apply hadd.trans
  congr 1
  · ring
  · ext;norm_num

theorem actual_source_reading_two_has_the_printed_latent_posterior_laws :
    (posteriorPairKernel 2).map Prod.fst = gaussianReal (8/5) (1/5) ∧
      (posteriorPairKernel 2).map Prod.snd = gaussianReal (4/5) (4/5) := by
  constructor
  · have h := actual_source_first_latent_marginal_of_the_posterior_pair_is_the_true_gaussian 2
    norm_num at h ⊢
    exact h
  · have h := actual_source_second_latent_marginal_of_the_posterior_pair_is_the_true_gaussian 2
    norm_num at h ⊢
    exact h

theorem actual_source_reading_two_latent_means_and_variances_are_the_true_integrals :
    (∫x:ℝ,x ∂(posteriorPairKernel 2).map Prod.fst)=8/5 ∧
      Var[id;(posteriorPairKernel 2).map Prod.fst]=1/5 ∧
      (∫x:ℝ,x ∂(posteriorPairKernel 2).map Prod.snd)=4/5 ∧
      Var[id;(posteriorPairKernel 2).map Prod.snd]=4/5 := by
  rw [actual_source_reading_two_has_the_printed_latent_posterior_laws.1,
    actual_source_reading_two_has_the_printed_latent_posterior_laws.2]
  simp [integral_id_gaussianReal,variance_id_gaussianReal]

end SafeLearning.CompleteModulesGPCorrelatedPosterior
