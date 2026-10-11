import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteModulesGaussianRegressionScalar

variable {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
variable (Y Z : Omega → ℝ)

def weight : ℝ := cov[Y,Z;P]/Var[Y;P]
def residual (omega : Omega) : ℝ := Z omega-weight P Y Z*Y omega

def residualPairLinear (w : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ-w • ContinuousLinearMap.fst ℝ ℝ ℝ)

lemma actual_joint_gaussian_observation_and_regression_residual_are_jointly_gaussian
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P) :
    HasGaussianLaw (fun omega => (Y omega,residual P Y Z omega)) P := by
  simpa [residualPairLinear,residual,smul_eq_mul] using
    hYZ.map_fun (residualPairLinear (weight P Y Z))

theorem actual_regression_residual_has_zero_covariance_with_the_observation
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P)
    (hvar : 0<Var[Y;P]) : cov[Y,residual P Y Z;P]=0 := by
  have hy := hYZ.fst.memLp_two
  have hz := hYZ.snd.memLp_two
  unfold residual
  rw [covariance_fun_sub_right hy hz (hy.const_mul _),
    covariance_const_mul_right,covariance_self hy.aemeasurable]
  unfold weight
  field_simp [hvar.ne']
  ring

theorem actual_joint_gaussian_regression_residual_is_independent_of_the_observation
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P)
    (hvar : 0<Var[Y;P]) : IndepFun Y (residual P Y Z) P := by
  have hg := actual_joint_gaussian_observation_and_regression_residual_are_jointly_gaussian P Y Z hYZ
  exact hg.indepFun_of_covariance_eq_zero
    (actual_regression_residual_has_zero_covariance_with_the_observation P Y Z hYZ hvar)

theorem actual_regression_residual_mean_and_variance_are_the_true_schur_expressions
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P)
    (hvar : 0<Var[Y;P]) :
    (∫ omega,residual P Y Z omega ∂P)= (∫ omega,Z omega ∂P)-weight P Y Z*(∫ omega,Y omega ∂P) ∧
    Var[residual P Y Z;P]=Var[Z;P]-cov[Y,Z;P] ^ 2/Var[Y;P] := by
  have hy := hYZ.fst.memLp_two
  have hz := hYZ.snd.memLp_two
  constructor
  · unfold residual
    rw [integral_sub hYZ.snd.integrable (hYZ.fst.integrable.const_mul _),integral_const_mul]
  · unfold residual
    rw [variance_fun_sub hz (hy.const_mul _),variance_const_mul,
      covariance_const_mul_right,covariance_comm Z Y]
    unfold weight
    field_simp [hvar.ne']
    ring

theorem actual_regression_residual_has_the_true_gaussian_law
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P)
    (hvar : 0<Var[Y;P]) :
    P.map (residual P Y Z)=gaussianReal
      ((∫ omega,Z omega ∂P)-weight P Y Z*(∫ omega,Y omega ∂P))
      (Var[Z;P]-cov[Y,Z;P] ^ 2/Var[Y;P]).toNNReal := by
  have h := (actual_joint_gaussian_observation_and_regression_residual_are_jointly_gaussian P Y Z hYZ).snd.map_eq_gaussianReal
  rw [(actual_regression_residual_mean_and_variance_are_the_true_schur_expressions P Y Z hYZ hvar).1,
    (actual_regression_residual_mean_and_variance_are_the_true_schur_expressions P Y Z hYZ hvar).2] at h
  exact h

def conditionalKernel (meanResidual w : ℝ) (varianceResidual : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨fun y => gaussianReal (meanResidual+w*y) varianceResidual,by fun_prop⟩
instance conditionalKernel_markov (meanResidual w : ℝ) (varianceResidual : ℝ≥0) :
    IsMarkovKernel (conditionalKernel meanResidual w varianceResidual) :=
  ⟨fun _ => by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩

lemma actual_independent_gaussian_residual_product_derives_the_conditional_joint
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (meanResidual w : ℝ) (varianceResidual : ℝ≥0) :
    (nu.prod (gaussianReal meanResidual varianceResidual)).map
        (fun pair : ℝ × ℝ => (pair.1,pair.2+w*pair.1)) =
      nu ⊗ₘ conditionalKernel meanResidual w varianceResidual := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻ pair,test (pair.1,pair.2+w*pair.1) ∂nu.prod (gaussianReal meanResidual varianceResidual))=_
  have hmtest : Measurable (fun pair : ℝ × ℝ => test (pair.1,pair.2+w*pair.1)) :=
    htest.comp (by fun_prop)
  rw [lintegral_prod _ hmtest.aemeasurable,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro y
  have ht : Measurable (fun z => test (y,z)) := htest.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ z,test (y,z+w*y) ∂gaussianReal meanResidual varianceResidual)=_
  have hm := gaussianReal_map_add_const (mu:=meanResidual) (v:=varianceResidual) (w*y)
  rw [conditionalKernel]
  change (∫⁻ z,test (y,z+w*y) ∂gaussianReal meanResidual varianceResidual)=
    ∫⁻ z,test (y,z) ∂gaussianReal (meanResidual+w*y) varianceResidual
  rw [← hm,lintegral_map ht (by fun_prop)]

theorem actual_arbitrary_joint_gaussian_has_the_true_scalar_schur_conditional_kernel
    (hYZ : HasGaussianLaw (fun omega => (Y omega,Z omega)) P)
    (hvar : 0<Var[Y;P]) :
    P.map (fun omega => (Y omega,Z omega)) =
      (P.map Y) ⊗ₘ conditionalKernel
        ((∫ omega,Z omega ∂P)-weight P Y Z*(∫ omega,Y omega ∂P)) (weight P Y Z)
        (Var[Z;P]-cov[Y,Z;P] ^ 2/Var[Y;P]).toNNReal := by
  have hg := actual_joint_gaussian_observation_and_regression_residual_are_jointly_gaussian P Y Z hYZ
  haveI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYZ.fst.aemeasurable).2 inferInstance
  have hi := actual_joint_gaussian_regression_residual_is_independent_of_the_observation P Y Z hYZ hvar
  have hp := hi.map_prod_eq_prod_map_map hYZ.fst.aemeasurable hg.snd.aemeasurable
  have hl := actual_regression_residual_has_the_true_gaussian_law P Y Z hYZ hvar
  have he : (P.map (fun omega => (Y omega,residual P Y Z omega))).map
      (fun pair : ℝ × ℝ => (pair.1,pair.2+weight P Y Z*pair.1)) =
      P.map (fun omega => (Y omega,Z omega)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hg.aemeasurable]
    congr 1
    funext omega
    simp [residual]
  rw [← he,hp,hl]
  exact actual_independent_gaussian_residual_product_derives_the_conditional_joint _ _ _ _

end SafeLearning.CompleteModulesGaussianRegressionScalar
