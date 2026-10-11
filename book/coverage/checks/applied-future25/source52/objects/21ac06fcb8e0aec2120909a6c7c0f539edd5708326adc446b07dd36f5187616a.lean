import SafeLearning.CompleteModulesGaussianRegressionFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianRegressionVector
open CompleteModulesGaussianRegressionFinite (observationCovariance crossCovariance)
variable {I J Omega : Type*} [Fintype I] [DecidableEq I] [Fintype J] [MeasurableSpace Omega]
variable (P : Measure Omega) [IsProbabilityMeasure P]
variable (Y : Omega → I → ℝ) (Z : Omega → J → ℝ)

def weight (j : J) : I → ℝ := (observationCovariance P Y)⁻¹*ᵥcrossCovariance P Y (fun o => Z o j)
def residual (o : Omega) (j : J) : ℝ := Z o j-weight P Y Z j ⬝ᵥY o

def residualPairLinear (w : J → I → ℝ) : ((I → ℝ) × (J → ℝ)) →L[ℝ] ((I → ℝ) × (J → ℝ)) :=
  (ContinuousLinearMap.fst ℝ (I → ℝ) (J → ℝ)).prod
    (ContinuousLinearMap.pi (fun j =>
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (I → ℝ) (J → ℝ)))-
        ∑ i,w j i • ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (I → ℝ) (J → ℝ)))))

theorem actual_old_observation_vector_and_each_query_are_jointly_gaussian
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (j : J) :
    HasGaussianLaw (fun o => (Y o,Z o j)) P := by
  let select : ((I → ℝ) × (J → ℝ)) →L[ℝ] ((I → ℝ) × ℝ) :=
    (ContinuousLinearMap.fst ℝ (I → ℝ) (J → ℝ)).prod
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (I → ℝ) (J → ℝ)))
  convert hYZ.map_fun select using 1 <;> rfl

theorem actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) :
    HasGaussianLaw (fun o => (Y o,residual P Y Z o)) P := by
  convert hYZ.map_fun (residualPairLinear (weight P Y Z)) using 1
  funext o
  apply Prod.ext
  · rfl
  · funext j
    simp [residualPairLinear,residual,dotProduct,smul_eq_mul]

theorem actual_old_vector_has_zero_covariance_with_every_query_residual
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) (i : I) (j : J) :
    cov[fun o => Y o i,fun o => residual P Y Z o j;P]=0 := by
  have hj := actual_old_observation_vector_and_each_query_are_jointly_gaussian P Y Z hYZ j
  exact CompleteModulesGaussianRegressionFinite.actual_finite_regression_residual_has_zero_covariance_with_every_observation
    P Y (fun o => Z o j) hj (weight P Y Z j)
    (CompleteModulesGaussianRegressionFinite.actual_inverse_covariance_coefficients_solve_the_true_covariance_system
      P Y (fun o => Z o j) hunit) i

theorem actual_old_observation_vector_is_independent_of_the_entire_query_residual_family
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) :
    IndepFun Y (residual P Y Z) P := by
  have hg := actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ
  exact hg.indepFun_of_covariance_eval (fun i j =>
    actual_old_vector_has_zero_covariance_with_every_query_residual P Y Z hYZ hunit i j)

theorem actual_query_residual_covariance_is_the_full_schur_covariance
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) (i j : J) :
    cov[fun o => residual P Y Z o i,fun o => residual P Y Z o j;P]=
      cov[fun o => Z o i,fun o => Z o j;P]-
        crossCovariance P Y (fun o => Z o i) ⬝ᵥ
          ((observationCovariance P Y)⁻¹*ᵥcrossCovariance P Y (fun o => Z o j)) := by
  have hy : ∀ k,MemLp (fun o => Y o k) 2 P := fun k => (hYZ.fst.eval k).memLp_two
  have hi := (hYZ.snd.eval i).memLp_two
  have hr := (actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ).snd.eval j
  have hsum : MemLp (fun o => ∑ k,weight P Y Z i k*Y o k) 2 P :=
    memLp_finsetSum _ (fun k _ => (hy k).const_mul _)
  have hz : ∀ k,cov[fun o => Y o k,fun o => residual P Y Z o j;P]=0 := fun k =>
    actual_old_vector_has_zero_covariance_with_every_query_residual P Y Z hYZ hunit k j
  have he : cov[fun o => residual P Y Z o i,fun o => residual P Y Z o j;P]=
      cov[fun o => Z o i,fun o => residual P Y Z o j;P] := by
    change cov[fun o => Z o i-∑ k,weight P Y Z i k*Y o k,fun o => residual P Y Z o j;P]=_
    rw [covariance_fun_sub_left hi hsum hr.memLp_two,
      covariance_fun_sum_left (fun k => (hy k).const_mul _) hr.memLp_two]
    simp [covariance_const_mul_left,hz]
  rw [he]
  have hsumj : MemLp (fun o => ∑ k,weight P Y Z j k*Y o k) 2 P :=
    memLp_finsetSum _ (fun k _ => (hy k).const_mul _)
  change cov[fun o => Z o i,fun o => Z o j-∑ k,weight P Y Z j k*Y o k;P]=_
  rw [covariance_fun_sub_right hi (hYZ.snd.eval j).memLp_two hsumj,
    covariance_fun_sum_right (fun k => (hy k).const_mul _) hi]
  simp_rw [covariance_const_mul_right]
  simp only [crossCovariance,weight,dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covariance_comm (fun o => Z o i)]
  ring

lemma actual_affine_finite_vector_pushforward_is_a_measurable_kernel
    (rho : Measure (J → ℝ)) [SFinite rho] (w : J → I → ℝ) :
    Measurable (fun y : I → ℝ => rho.map (fun r : J → ℝ => r+(fun j => w j ⬝ᵥy))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : (fun y : I → ℝ => (rho.map (fun r : J → ℝ => r+(fun j => w j ⬝ᵥy))) s)=
      (fun y => rho (Prod.mk y ⁻¹' ((fun pair : (I → ℝ) × (J → ℝ) => pair.2+(fun j => w j ⬝ᵥpair.1)) ⁻¹' s))) := by
    funext y
    rw [Measure.map_apply (by fun_prop) hs]
    rfl
  rw [he]
  exact measurable_measure_prodMk_left
    ((show Measurable (fun pair : (I → ℝ) × (J → ℝ) => pair.2+(fun j => w j ⬝ᵥpair.1)) by
      simp only [dotProduct];fun_prop) hs)

def affineKernel (rho : Measure (J → ℝ)) [SFinite rho] (w : J → I → ℝ) : Kernel (I → ℝ) (J → ℝ) :=
  ⟨fun y => rho.map (fun r : J → ℝ => r+(fun j => w j ⬝ᵥy)),
    actual_affine_finite_vector_pushforward_is_a_measurable_kernel rho w⟩
instance affineKernel_markov (rho : Measure (J → ℝ)) [IsProbabilityMeasure rho] (w : J → I → ℝ) :
    IsMarkovKernel (affineKernel rho w) :=
  ⟨fun y => by dsimp [affineKernel];infer_instance⟩

def conditionalKernel : Kernel (I → ℝ) (J → ℝ) :=
  affineKernel (P.map (residual P Y Z)) (weight P Y Z)

lemma actual_independent_vector_residual_product_derives_the_finite_affine_conditional_joint
    (nu : Measure (I → ℝ)) [IsProbabilityMeasure nu]
    (rho : Measure (J → ℝ)) [IsProbabilityMeasure rho] (w : J → I → ℝ) :
    (nu.prod rho).map (fun pair : (I → ℝ) × (J → ℝ) => (pair.1,pair.2+(fun j => w j ⬝ᵥpair.1)))=
      nu ⊗ₘ affineKernel rho w := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by simp only [dotProduct];fun_prop)]
  change (∫⁻ pair,test (pair.1,pair.2+(fun j => w j ⬝ᵥpair.1)) ∂nu.prod rho)=_
  have hm : Measurable (fun pair : (I → ℝ) × (J → ℝ) => test (pair.1,pair.2+(fun j => w j ⬝ᵥpair.1))) :=
    htest.comp (by simp only [dotProduct];fun_prop)
  rw [lintegral_prod _ hm.aemeasurable,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro y
  change (∫⁻ r,test (y,r+(fun j => w j ⬝ᵥy)) ∂rho)=
    ∫⁻ r,test (y,r) ∂rho.map (fun r => r+(fun j => w j ⬝ᵥy))
  have ht : Measurable (fun r : J → ℝ => test (y,r)) :=
    htest.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map ht (by fun_prop)]

theorem actual_old_observation_vector_derives_the_true_entire_query_family_conditional_joint
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) :
    P.map (fun o => (Y o,Z o))=(P.map Y) ⊗ₘ conditionalKernel P Y Z := by
  have hg := actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ
  haveI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYZ.fst.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hg.snd.aemeasurable).2 inferInstance
  have hi := actual_old_observation_vector_is_independent_of_the_entire_query_residual_family P Y Z hYZ hunit
  have hp := hi.map_prod_eq_prod_map_map hYZ.fst.aemeasurable hg.snd.aemeasurable
  have he : (P.map (fun o => (Y o,residual P Y Z o))).map
      (fun pair : (I → ℝ) × (J → ℝ) => (pair.1,pair.2+(fun j => weight P Y Z j ⬝ᵥpair.1)))=
      P.map (fun o => (Y o,Z o)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by simp only [dotProduct];fun_prop) hg.aemeasurable]
    congr 1
    funext o
    apply Prod.ext
    · rfl
    · funext j
      simp [residual]
  rw [←he,hp]
  exact actual_independent_vector_residual_product_derives_the_finite_affine_conditional_joint _ _ _

theorem actual_first_stage_finite_query_posterior_is_again_gaussian_at_every_observation_vector
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (y : I → ℝ) :
    IsGaussian (conditionalKernel P Y Z y) := by
  have hg := actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ
  haveI := hg.snd.isGaussian_map
  dsimp [conditionalKernel,affineKernel]
  infer_instance

theorem actual_first_stage_query_covariance_is_the_full_schur_covariance_at_every_observation_vector
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) (y : I → ℝ) (i j : J) :
    cov[fun r => r i,fun r => r j;conditionalKernel P Y Z y]=
      cov[fun o => Z o i,fun o => Z o j;P]-
        crossCovariance P Y (fun o => Z o i) ⬝ᵥ
          ((observationCovariance P Y)⁻¹*ᵥcrossCovariance P Y (fun o => Z o j)) := by
  have hg := actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hg.snd.aemeasurable).2 inferInstance
  haveI := hg.snd.isGaussian_map
  have hi : Integrable (fun r : J → ℝ => r i) (P.map (residual P Y Z)) :=
    (IsGaussian.hasGaussianLaw_id.eval i).integrable
  have hj : Integrable (fun r : J → ℝ => r j) (P.map (residual P Y Z)) :=
    (IsGaussian.hasGaussianLaw_id.eval j).integrable
  dsimp [conditionalKernel,affineKernel]
  rw [covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (by fun_prop)]
  simp only [Pi.add_apply]
  rw [covariance_add_const_left hi _,covariance_add_const_right hj _,
    covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable hg.snd.aemeasurable]
  exact actual_query_residual_covariance_is_the_full_schur_covariance P Y Z hYZ hunit i j

theorem actual_first_stage_query_means_are_the_true_regression_means
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) (y : I → ℝ) (j : J) :
    (∫ r,r j ∂conditionalKernel P Y Z y)=
      (∫ o,Z o j ∂P)-∑ i,weight P Y Z j i*(∫ o,Y o i ∂P)+weight P Y Z j ⬝ᵥy := by
  have hg := actual_old_vector_and_entire_query_residual_family_are_jointly_gaussian P Y Z hYZ
  have hj := actual_old_observation_vector_and_each_query_are_jointly_gaussian P Y Z hYZ j
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hg.snd.aemeasurable).2 inferInstance
  haveI := hg.snd.isGaussian_map
  have hi : Integrable (fun r : J → ℝ => r j) (P.map (residual P Y Z)) :=
    (IsGaussian.hasGaussianLaw_id.eval j).integrable
  dsimp [conditionalKernel,affineKernel]
  rw [integral_map
    (show AEMeasurable (fun r : J → ℝ => r+(fun k => weight P Y Z k ⬝ᵥy))
      (P.map (residual P Y Z)) by fun_prop)
    (measurable_pi_apply j).aestronglyMeasurable]
  simp only [Pi.add_apply]
  rw [integral_add hi (integrable_const _),integral_const]
  simp only [probReal_univ,one_smul]
  rw [integral_map hg.snd.aemeasurable (measurable_pi_apply j).aestronglyMeasurable]
  exact congrArg (fun m : ℝ => m+weight P Y Z j ⬝ᵥy)
    (CompleteModulesGaussianRegressionFinite.actual_finite_regression_mean_and_variance_are_the_true_schur_expressions
      P Y (fun o => Z o j) hj (weight P Y Z j)
      (CompleteModulesGaussianRegressionFinite.actual_inverse_covariance_coefficients_solve_the_true_covariance_system
        P Y (fun o => Z o j) hunit)).1

end SafeLearning.CompleteModulesGaussianRegressionVector
