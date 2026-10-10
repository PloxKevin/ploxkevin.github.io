import SafeLearning.CompleteAppliedGaussianFourJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianFourGenerative
open CompleteAppliedGaussianFourUpdate CompleteAppliedGaussianFourJoint

def noiseLaw : Measure Readings :=
  (gaussianReal 0 (1/4)).prod ((gaussianReal 0 (1/4)).prod
    ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4))))
def noiseTuple {Ω : Type*} (noise : Fin 4→Ω→ℝ) (omega : Ω) : Readings :=
  (noise 0 omega,(noise 1 omega,(noise 2 omega,noise 3 omega)))
def generateReadings (pair : ℝ×Readings) : ℝ×Readings :=
  (pair.1,(pair.1+pair.2.1,(pair.1+pair.2.2.1,
    (pair.1+pair.2.2.2.1,pair.1+pair.2.2.2.2))))

instance noiseLaw_probability : IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw;infer_instance

theorem actual_iid_four_gaussian_noises_have_the_true_product_tuple_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (noise : Fin 4→Ω→ℝ) (hindep : iIndepFun noise P)
    (hlaw : ∀i,HasLaw (noise i) (gaussianReal 0 (1/4)) P) :
    HasLaw (noiseTuple noise) noiseLaw P := by
  have hmeas : ∀i,AEMeasurable (noise i) P:=fun i=>(hlaw i).aemeasurable
  have h01:=(hindep.indepFun (show (0:Fin 4)≠1 by decide)).hasLaw_prod (hlaw 0) (hlaw 1)
  have h23:=(hindep.indepFun (show (2:Fin 4)≠3 by decide)).hasLaw_prod (hlaw 2) (hlaw 3)
  have hpair:=(hindep.indepFun_prodMk_prodMk₀ hmeas 0 1 2 3
    (by decide) (by decide) (by decide) (by decide)).hasLaw_prod h01 h23
  have hassoc : HasLaw
      (MeasurableEquiv.prodAssoc : (ℝ×ℝ)×(ℝ×ℝ)→Readings) noiseLaw
      (((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4))).prod
        ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4)))) :=
    (measurePreserving_prodAssoc _ _ _).hasLaw
  exact hassoc.comp hpair

theorem actual_four_noise_translation_is_the_conditional_reading_kernel (latent : ℝ) :
    noiseLaw.map (fun y:Readings=>(latent+y.1,(latent+y.2.1,
      (latent+y.2.2.1,latent+y.2.2.2))))=readingKernel latent := by
  have h2 : ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4))).map
      (fun y:ℝ×ℝ=>(latent+y.1,latent+y.2))=
        (gaussianReal latent (1/4)).prod (gaussianReal latent (1/4)) := by
    have h:=Measure.map_prod_map (gaussianReal 0 (1/4)) (gaussianReal 0 (1/4))
      (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
      (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
    simp only [gaussianReal_map_const_add,zero_add] at h
    exact h.symm
  have h3 : ((gaussianReal 0 (1/4)).prod
      ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4)))).map
      (fun y:ℝ×(ℝ×ℝ)=>(latent+y.1,(latent+y.2.1,latent+y.2.2)))=
        (gaussianReal latent (1/4)).prod
          ((gaussianReal latent (1/4)).prod (gaussianReal latent (1/4))) := by
    have h:=Measure.map_prod_map (gaussianReal 0 (1/4))
      ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4)))
      (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
      (show Measurable (fun noise:ℝ×ℝ=>(latent+noise.1,latent+noise.2)) by fun_prop)
    rw [gaussianReal_map_const_add,h2] at h
    simp only [zero_add] at h
    exact h.symm
  have h:=Measure.map_prod_map (gaussianReal 0 (1/4))
    ((gaussianReal 0 (1/4)).prod ((gaussianReal 0 (1/4)).prod (gaussianReal 0 (1/4))))
    (show Measurable (fun noise:ℝ=>latent+noise) by fun_prop)
    (show Measurable (fun noise:ℝ×(ℝ×ℝ)=>(latent+noise.1,(latent+noise.2.1,latent+noise.2.2))) by fun_prop)
  rw [gaussianReal_map_const_add,h3] at h
  simp only [zero_add] at h
  simp only [readingKernel,Kernel.prod_apply]
  change noiseLaw.map _=(gaussianReal latent (1/4)).prod
    ((gaussianReal latent (1/4)).prod ((gaussianReal latent (1/4)).prod (gaussianReal latent (1/4))))
  exact h.symm

theorem actual_independent_prior_and_four_iid_noises_construct_the_full_joint :
    ((gaussianReal 0 1).prod noiseLaw).map generateReadings=fullJoint := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by unfold generateReadings;fun_prop)]
  change (∫⁻pair,(test ∘ generateReadings) pair ∂(gaussianReal 0 1).prod noiseLaw)=_
  rw [lintegral_prod _ (by unfold generateReadings;fun_prop),fullJoint,
    Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro latent
  have ht : Measurable (fun y:Readings=>test (latent,y)):=htest.comp measurable_prodMk_left
  have hm:=actual_four_noise_translation_is_the_conditional_reading_kernel latent
  have hi:=lintegral_map ht
    (show Measurable (fun y:Readings=>(latent+y.1,(latent+y.2.1,
      (latent+y.2.2.1,latent+y.2.2.2)))) by fun_prop) (μ:=noiseLaw)
  rw [hm] at hi
  exact hi.symm

theorem actual_arbitrary_independent_prior_and_iid_noise_model_has_the_full_data_disintegration
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (latent : Ω→ℝ) (noise : Fin 4→Ω→ℝ)
    (hprior : HasLaw latent (gaussianReal 0 1) P)
    (hlaw : ∀i,HasLaw (noise i) (gaussianReal 0 (1/4)) P)
    (hiid : iIndepFun noise P) (hindep : IndepFun latent (noiseTuple noise) P) :
    HasLaw (fun omega=>(latent omega,
      (latent omega+noise 0 omega,(latent omega+noise 1 omega,
        (latent omega+noise 2 omega,latent omega+noise 3 omega))))) fullJoint P ∧
    HasLaw (fun omega=>((latent omega+noise 0 omega,(latent omega+noise 1 omega,
      (latent omega+noise 2 omega,latent omega+noise 3 omega))),latent omega))
        (dataLaw ⊗ₘ fullPosteriorKernel) P := by
  have hn:=actual_iid_four_gaussian_noises_have_the_true_product_tuple_law noise hiid hlaw
  have hp:=hindep.hasLaw_prod hprior hn
  have hg : HasLaw generateReadings fullJoint ((gaussianReal 0 1).prod noiseLaw) :=
    ⟨(show Measurable generateReadings by unfold generateReadings;fun_prop).aemeasurable,
      actual_independent_prior_and_four_iid_noises_construct_the_full_joint⟩
  have hj:=hg.comp hp
  have hs : HasLaw Prod.swap (dataLaw ⊗ₘ fullPosteriorKernel) fullJoint :=
    ⟨measurable_swap.aemeasurable,
      actual_reversed_full_generative_joint_derives_the_four_data_conditional_kernel⟩
  exact ⟨hj,hs.comp hj⟩

end SafeLearning.CompleteAppliedGaussianFourGenerative
