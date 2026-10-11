import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianRankOne
variable {I Omega : Type*} [Fintype I] [MeasurableSpace Omega]
variable (P : Measure Omega) [IsProbabilityMeasure P]
variable (Y : Omega → ℝ) (Z : Omega → I → ℝ)

def weight (i : I) : ℝ := cov[Y,fun o => Z o i;P]/Var[Y;P]
def residual (o : Omega) (i : I) : ℝ := Z o i-weight P Y Z i*Y o
def residualPairLinear (w : I → ℝ) : (ℝ × (I → ℝ)) →L[ℝ] (ℝ × (I → ℝ)) :=
  (ContinuousLinearMap.fst ℝ ℝ (I → ℝ)).prod
    (ContinuousLinearMap.pi (fun i =>
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (I → ℝ)))-
        w i • ContinuousLinearMap.fst ℝ ℝ (I → ℝ)))

theorem actual_one_observation_and_all_query_regression_residuals_are_jointly_gaussian
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) :
    HasGaussianLaw (fun o => (Y o,residual P Y Z o)) P := by
  convert hYZ.map_fun (residualPairLinear (weight P Y Z)) using 1 <;> rfl

theorem actual_one_observation_has_zero_covariance_with_every_query_residual
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P]) (i : I) :
    cov[Y,fun o => residual P Y Z o i;P]=0 := by
  have hy := hYZ.fst.memLp_two
  have hz := (hYZ.snd.eval i).memLp_two
  unfold residual
  rw [covariance_fun_sub_right hy hz (hy.const_mul _),covariance_const_mul_right,
    covariance_self hYZ.fst.aemeasurable]
  unfold weight
  field_simp [hvar.ne']
  ring

theorem actual_one_observation_is_independent_of_the_entire_query_residual_vector
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P]) :
    IndepFun Y (residual P Y Z) P := by
  have hg := actual_one_observation_and_all_query_regression_residuals_are_jointly_gaussian P Y Z hYZ
  let lift : (ℝ × (I → ℝ)) →L[ℝ] ((Unit → ℝ) × (I → ℝ)) :=
    (ContinuousLinearMap.pi (fun _ : Unit => ContinuousLinearMap.fst ℝ ℝ (I → ℝ))).prod
      (ContinuousLinearMap.snd ℝ ℝ (I → ℝ))
  have hl : HasGaussianLaw (fun o => (fun _ : Unit => Y o,residual P Y Z o)) P := by
    simpa [lift] using hg.map_fun lift
  have hi := hl.indepFun_of_covariance_eval (fun _ i =>
    actual_one_observation_has_zero_covariance_with_every_query_residual P Y Z hYZ hvar i)
  convert hi.comp (measurable_pi_apply ()) measurable_id using 1 <;> rfl

theorem actual_two_query_residual_covariance_is_the_literal_rank_one_update
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P]) (i j : I) :
    cov[fun o => residual P Y Z o i,fun o => residual P Y Z o j;P]=
      cov[fun o => Z o i,fun o => Z o j;P]-
        cov[fun o => Z o i,Y;P]*cov[Y,fun o => Z o j;P]/Var[Y;P] := by
  have hy := hYZ.fst.memLp_two
  have hi := (hYZ.snd.eval i).memLp_two
  have hj := (hYZ.snd.eval j).memLp_two
  unfold residual
  rw [covariance_fun_sub_fun_sub hi (hy.const_mul _) hj (hy.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    covariance_self hYZ.fst.aemeasurable]
  unfold weight
  rw [covariance_comm (fun o => Z o i) Y]
  field_simp [hvar.ne']
  ring

lemma actual_affine_pushforward_of_a_fixed_measure_is_a_measurable_kernel
    (rho : Measure (I → ℝ)) [SFinite rho] (w : I → ℝ) :
    Measurable (fun y : ℝ => rho.map (fun r : I → ℝ => r+(fun i => w i*y))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [Measure.map_apply (by fun_prop) hs]
  exact measurable_measure_prodMk_left
    ((show Measurable (fun pair : ℝ × (I → ℝ) => pair.2+(fun i => w i*pair.1)) by fun_prop) hs)

def conditionalKernel : Kernel ℝ (I → ℝ) :=
  ⟨fun y => (P.map (residual P Y Z)).map
      (fun r : I → ℝ => r+(fun i => weight P Y Z i*y)),
    actual_affine_pushforward_of_a_fixed_measure_is_a_measurable_kernel _ _⟩

theorem actual_conditional_kernel_is_markov
    (hresidual : AEMeasurable (residual P Y Z) P) :
    IsMarkovKernel (conditionalKernel P Y Z) := by
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hresidual).2 inferInstance
  exact ⟨fun y => by dsimp [conditionalKernel];infer_instance⟩

lemma actual_independent_vector_residual_product_derives_the_affine_conditional_joint
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (rho : Measure (I → ℝ)) [IsProbabilityMeasure rho] (w : I → ℝ) :
    (nu.prod rho).map (fun pair : ℝ × (I → ℝ) => (pair.1,pair.2+(fun i => w i*pair.1)))=
      nu ⊗ₘ (⟨fun y => rho.map (fun r => r+(fun i => w i*y)),
        actual_affine_pushforward_of_a_fixed_measure_is_a_measurable_kernel _ _⟩ : Kernel ℝ (I → ℝ)) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻ pair,test (pair.1,pair.2+(fun i => w i*pair.1)) ∂nu.prod rho)=_
  have hm : Measurable (fun pair : ℝ × (I → ℝ) => test (pair.1,pair.2+(fun i => w i*pair.1))) :=
    htest.comp (by fun_prop)
  rw [lintegral_prod _ hm.aemeasurable,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro y
  change (∫⁻ r,test (y,r+(fun i => w i*y)) ∂rho)=
    ∫⁻ r,test (y,r) ∂rho.map (fun r => r+(fun i => w i*y))
  have ht : Measurable (fun r : I → ℝ => test (y,r)) :=
    htest.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map ht (by fun_prop)]

theorem actual_finite_query_gaussian_family_has_the_true_one_observation_conditional_joint
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P]) :
    P.map (fun o => (Y o,Z o))=(P.map Y) ⊗ₘ conditionalKernel P Y Z := by
  have hg := actual_one_observation_and_all_query_regression_residuals_are_jointly_gaussian P Y Z hYZ
  haveI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYZ.fst.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hg.snd.aemeasurable).2 inferInstance
  have hi := actual_one_observation_is_independent_of_the_entire_query_residual_vector P Y Z hYZ hvar
  have hp := hi.map_prod_eq_prod_map_map hYZ.fst.aemeasurable hg.snd.aemeasurable
  have he : (P.map (fun o => (Y o,residual P Y Z o))).map
      (fun pair : ℝ × (I → ℝ) => (pair.1,pair.2+(fun i => weight P Y Z i*pair.1)))=
      P.map (fun o => (Y o,Z o)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hg.aemeasurable]
    congr 1
    funext o
    congr 1
    funext i
    simp [residual]
  rw [← he,hp]
  exact actual_independent_vector_residual_product_derives_the_affine_conditional_joint _ _ _

theorem actual_conditioned_finite_query_family_is_again_gaussian_at_every_observed_value
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (y : ℝ) :
    IsGaussian (conditionalKernel P Y Z y) := by
  have hg := actual_one_observation_and_all_query_regression_residuals_are_jointly_gaussian P Y Z hYZ
  haveI := hg.snd.isGaussian_map
  dsimp [conditionalKernel]
  infer_instance

theorem actual_conditional_query_covariance_is_the_literal_rank_one_update_at_every_observed_value
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P])
    (y : ℝ) (i j : I) :
    cov[fun r => r i,fun r => r j;conditionalKernel P Y Z y]=
      cov[fun o => Z o i,fun o => Z o j;P]-
        cov[fun o => Z o i,Y;P]*cov[Y,fun o => Z o j;P]/Var[Y;P] := by
  have hg := actual_one_observation_and_all_query_regression_residuals_are_jointly_gaussian P Y Z hYZ
  haveI : IsProbabilityMeasure (P.map (residual P Y Z)) :=
    (Measure.isProbabilityMeasure_map_iff hg.snd.aemeasurable).2 inferInstance
  haveI := hg.snd.isGaussian_map
  have hi : Integrable (fun r : I → ℝ => r i) (P.map (residual P Y Z)) :=
    (IsGaussian.hasGaussianLaw_id.eval i).integrable
  have hj : Integrable (fun r : I → ℝ => r j) (P.map (residual P Y Z)) :=
    (IsGaussian.hasGaussianLaw_id.eval j).integrable
  dsimp [conditionalKernel]
  rw [covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (by fun_prop)]
  simp only [Pi.add_apply]
  rw [covariance_add_const_left hi _ ,covariance_add_const_right hj _,
    covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable hg.snd.aemeasurable]
  exact actual_two_query_residual_covariance_is_the_literal_rank_one_update P Y Z hYZ hvar i j

theorem actual_conditional_variance_never_increases_at_any_query_or_observed_value
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (hvar : 0<Var[Y;P])
    (y : ℝ) (i : I) :
    Var[fun r => r i;conditionalKernel P Y Z y]≤Var[fun o => Z o i;P] := by
  have h := actual_conditional_query_covariance_is_the_literal_rank_one_update_at_every_observed_value
    P Y Z hYZ hvar y i i
  rw [covariance_self (measurable_pi_apply i).aemeasurable,covariance_self (hYZ.snd.eval i).aemeasurable,
    covariance_comm (fun o => Z o i) Y] at h
  rw [h]
  have hn : 0≤cov[Y,fun o => Z o i;P]*cov[Y,fun o => Z o i;P]/Var[Y;P] :=
    div_nonneg (mul_self_nonneg _) hvar.le
  linarith

end SafeLearning.CompleteModulesGaussianRankOne
