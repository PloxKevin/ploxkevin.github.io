import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteModulesGPCorrelatedPrior

def baseLaw : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 (3/4))
def sourceLatentPair (az : ℝ × ℝ) : ℝ × ℝ := (az.1,(1/2)*az.1+az.2)
def sourcePriorLaw : Measure (ℝ × ℝ) := baseLaw.map sourceLatentPair
instance baseLaw_probability : IsProbabilityMeasure baseLaw := by unfold baseLaw;infer_instance
instance sourcePriorLaw_probability : IsProbabilityMeasure sourcePriorLaw := by
  unfold sourcePriorLaw
  apply (Measure.isProbabilityMeasure_map_iff (show AEMeasurable sourceLatentPair baseLaw by
    exact (show Measurable sourceLatentPair by unfold sourceLatentPair;fun_prop).aemeasurable)).2
  infer_instance

lemma actual_base_first_coordinate_has_its_gaussian_law :
    HasLaw Prod.fst (gaussianReal 0 1) baseLaw :=
  ⟨measurable_fst.aemeasurable,by simp [baseLaw]⟩
lemma actual_base_second_coordinate_has_its_independent_residual_gaussian_law :
    HasLaw Prod.snd (gaussianReal 0 (3/4)) baseLaw :=
  ⟨measurable_snd.aemeasurable,by simp [baseLaw]⟩

theorem actual_every_source_prior_linear_combination_has_the_true_gaussian_law
    (u v : ℝ) :
    sourcePriorLaw.map (fun pair : ℝ × ℝ => u*pair.1+v*pair.2) =
      gaussianReal 0 (NNReal.mk ((u+v/2)^2) (sq_nonneg _) + NNReal.mk (v^2) (sq_nonneg _) * (3/4)) := by
  have ha := gaussianReal_const_mul actual_base_first_coordinate_has_its_gaussian_law (u+v/2)
  have hz := gaussianReal_const_mul actual_base_second_coordinate_has_its_independent_residual_gaussian_law v
  have hi : IndepFun (fun az : ℝ × ℝ => (u+v/2)*az.1) (fun az : ℝ × ℝ => v*az.2) baseLaw := by
    unfold baseLaw
    exact indepFun_prod (by fun_prop) (by fun_prop)
  have hs := gaussianReal_add_gaussianReal_of_indepFun hi ha hz
  rw [sourcePriorLaw,Measure.map_map (by fun_prop) (by unfold sourceLatentPair;fun_prop)]
  have hf : (fun az : ℝ × ℝ => u*(sourceLatentPair az).1+v*(sourceLatentPair az).2) =
      (fun az : ℝ × ℝ => (u+v/2)*az.1)+(fun az : ℝ × ℝ => v*az.2) := by
    funext az;unfold sourceLatentPair;simp only [Pi.add_apply];ring
  change baseLaw.map (fun az : ℝ × ℝ => u*(sourceLatentPair az).1+v*(sourceLatentPair az).2) = _
  rw [hf,hs]
  congr 1
  · ring
  · simp

theorem actual_source_prior_quadratic_variance_is_the_displayed_gram_form (u v : ℝ) :
    ((NNReal.mk ((u+v/2)^2) (sq_nonneg _) + NNReal.mk (v^2) (sq_nonneg _) * (3/4)) : ℝ)=
      u^2+u*v+v^2 := by
  norm_num
  ring

theorem actual_source_both_latent_marginals_have_unit_prior_gaussian_laws :
    sourcePriorLaw.map Prod.fst = gaussianReal 0 1 ∧
      sourcePriorLaw.map Prod.snd = gaussianReal 0 1 := by
  constructor
  · have h := actual_every_source_prior_linear_combination_has_the_true_gaussian_law 1 0
    norm_num at h
    exact h
  · have h := actual_every_source_prior_linear_combination_has_the_true_gaussian_law 0 1
    have hv : NNReal.mk (((0:ℝ)+1/2)^2) (sq_nonneg _) +
        NNReal.mk ((1:ℝ)^2) (sq_nonneg _) * (3/4) = 1 := by
      ext
      norm_num
    rw [hv] at h
    norm_num at h
    exact h

theorem actual_source_prior_covariance_is_exactly_one_half :
    cov[Prod.fst,Prod.snd;sourcePriorLaw] = 1/2 := by
  have ha : HasLaw Prod.fst (gaussianReal 0 1) sourcePriorLaw :=
    ⟨measurable_fst.aemeasurable,actual_source_both_latent_marginals_have_unit_prior_gaussian_laws.1⟩
  have hb : HasLaw Prod.snd (gaussianReal 0 1) sourcePriorLaw :=
    ⟨measurable_snd.aemeasurable,actual_source_both_latent_marginals_have_unit_prior_gaussian_laws.2⟩
  have hsum : HasLaw (Prod.fst+Prod.snd) (gaussianReal 0 3) sourcePriorLaw := by
    refine ⟨by fun_prop,?_⟩
    have h := actual_every_source_prior_linear_combination_has_the_true_gaussian_law 1 1
    have hv : NNReal.mk (((1:ℝ)+1/2)^2) (sq_nonneg _) +
        NNReal.mk ((1:ℝ)^2) (sq_nonneg _) * (3/4) = 3 := by
      ext
      norm_num
    rw [hv] at h
    norm_num at h
    exact h
  have hlpa : MemLp Prod.fst 2 sourcePriorLaw := ha.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hlpb : MemLp Prod.snd 2 sourcePriorLaw := hb.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  have hvar := variance_add hlpa hlpb
  rw [ha.variance_eq,hb.variance_eq,hsum.variance_eq] at hvar
  simp only [variance_id_gaussianReal] at hvar
  norm_num at hvar
  linarith

end SafeLearning.CompleteModulesGPCorrelatedPrior
