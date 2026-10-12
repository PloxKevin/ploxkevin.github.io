import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianRegressionFinite

variable {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
variable (P : Measure Omega) [IsProbabilityMeasure P]
variable (Y : Omega → I → ℝ) (Z : Omega → ℝ)

def observationCovariance : Matrix I I ℝ := fun i j => cov[fun o => Y o i,fun o => Y o j;P]
def crossCovariance : I → ℝ := fun i => cov[fun o => Y o i,Z;P]
def residual (w : I → ℝ) (o : Omega) : ℝ := Z o-∑ i,w i*Y o i

def residualPairLinear (w : I → ℝ) : ((I → ℝ) × ℝ) →L[ℝ] ((I → ℝ) × ℝ) :=
  (ContinuousLinearMap.fst ℝ (I → ℝ) ℝ).prod
    ((ContinuousLinearMap.snd ℝ (I → ℝ) ℝ)-
      ∑ i,w i • ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (I → ℝ) ℝ)))

theorem actual_finite_gaussian_observations_and_regression_residual_are_jointly_gaussian
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (w : I → ℝ) :
    HasGaussianLaw (fun o => (Y o,residual Y Z w o)) P := by
  simpa [residualPairLinear,residual,smul_eq_mul] using hYZ.map_fun (residualPairLinear w)

theorem actual_inverse_covariance_coefficients_solve_the_true_covariance_system
    (hunit : IsUnit (observationCovariance P Y)) :
    observationCovariance P Y *ᵥ
        ((observationCovariance P Y)⁻¹ *ᵥ crossCovariance P Y Z)=crossCovariance P Y Z := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det.mp hunit),Matrix.one_mulVec]

theorem actual_finite_regression_residual_has_zero_covariance_with_every_observation
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (w : I → ℝ)
    (hsolve : observationCovariance P Y *ᵥ w=crossCovariance P Y Z) (i : I) :
    cov[fun o => Y o i,residual Y Z w;P]=0 := by
  have hy : ∀ j,MemLp (fun o => Y o j) 2 P := fun j => (hYZ.fst.eval j).memLp_two
  have hsum : MemLp (fun o => ∑ j,w j*Y o j) 2 P := by
    exact memLp_finsetSum _ (fun j _ => (hy j).const_mul _)
  unfold residual
  rw [covariance_fun_sub_right (hy i) hYZ.snd.memLp_two hsum,
    covariance_fun_sum_right (fun j => (hy j).const_mul _) (hy i)]
  simp_rw [covariance_const_mul_right]
  have hs := congrFun hsolve i
  change (∑ j,observationCovariance P Y i j*w j)=crossCovariance P Y Z i at hs
  simpa [observationCovariance,crossCovariance,mul_comm] using sub_eq_zero.mpr hs.symm

theorem actual_finite_gaussian_regression_residual_is_independent_of_the_whole_observation_vector
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (w : I → ℝ)
    (hsolve : observationCovariance P Y *ᵥ w=crossCovariance P Y Z) :
    IndepFun Y (residual Y Z w) P := by
  have hg := actual_finite_gaussian_observations_and_regression_residual_are_jointly_gaussian P Y Z hYZ w
  let lift : ((I → ℝ) × ℝ) →L[ℝ] ((I → ℝ) × (Unit → ℝ)) :=
    (ContinuousLinearMap.fst ℝ (I → ℝ) ℝ).prod
      (ContinuousLinearMap.pi (fun _ : Unit => ContinuousLinearMap.snd ℝ (I → ℝ) ℝ))
  have hl : HasGaussianLaw (fun o => (Y o,fun _ : Unit => residual Y Z w o)) P := by
    simpa [lift] using hg.map_fun lift
  have hi := hl.indepFun_of_covariance_eval (fun i _ =>
    actual_finite_regression_residual_has_zero_covariance_with_every_observation P Y Z hYZ w hsolve i)
  simpa only [Function.comp_def] using hi.comp measurable_id (measurable_pi_apply ())

theorem actual_finite_regression_mean_and_variance_are_the_true_schur_expressions
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P) (w : I → ℝ)
    (hsolve : observationCovariance P Y *ᵥ w=crossCovariance P Y Z) :
    (∫ o,residual Y Z w o ∂P)= (∫ o,Z o ∂P)-∑ i,w i*(∫ o,Y o i ∂P) ∧
    Var[residual Y Z w;P]=Var[Z;P]-w ⬝ᵥ crossCovariance P Y Z := by
  have hy : ∀ j,MemLp (fun o => Y o j) 2 P := fun j => (hYZ.fst.eval j).memLp_two
  have hsum : MemLp (fun o => ∑ j,w j*Y o j) 2 P := by
    exact memLp_finsetSum _ (fun j _ => (hy j).const_mul _)
  have hr := (actual_finite_gaussian_observations_and_regression_residual_are_jointly_gaussian P Y Z hYZ w).snd
  have hz := hYZ.snd.memLp_two
  constructor
  · unfold residual
    rw [integral_sub hYZ.snd.integrable (hsum.integrable (by norm_num)),
      integral_finsetSum _ (fun j _ => (hYZ.fst.eval j).integrable.const_mul _)]
    simp_rw [integral_const_mul]
  · have hzero : ∀ i,cov[fun o => Y o i,residual Y Z w;P]=0 := fun i =>
      actual_finite_regression_residual_has_zero_covariance_with_every_observation P Y Z hYZ w hsolve i
    have hvar : cov[residual Y Z w,residual Y Z w;P]=
        cov[Z,residual Y Z w;P] := by
      change cov[fun o => Z o-∑ i,w i*Y o i,residual Y Z w;P]=_
      rw [covariance_fun_sub_left hz hsum hr.memLp_two,
        covariance_fun_sum_left (fun j => (hy j).const_mul _) hr.memLp_two]
      simp [covariance_const_mul_left,hzero]
    rw [covariance_self hr.aemeasurable] at hvar
    rw [hvar]
    unfold residual
    rw [covariance_fun_sub_right hz hz hsum,
      covariance_fun_sum_right (fun j => (hy j).const_mul _) hz,
      covariance_self hYZ.snd.aemeasurable]
    simp [dotProduct,crossCovariance,covariance_const_mul_right,covariance_const_mul_left,covariance_comm Z]

def conditionalKernel (meanResidual : ℝ) (w : I → ℝ) (varianceResidual : ℝ≥0) :
    Kernel (I → ℝ) ℝ :=
  ⟨fun y => gaussianReal (meanResidual+w ⬝ᵥ y) varianceResidual,by fun_prop⟩
instance conditionalKernel_markov (meanResidual : ℝ) (w : I → ℝ) (varianceResidual : ℝ≥0) :
    IsMarkovKernel (conditionalKernel meanResidual w varianceResidual) :=
  ⟨fun _ => by change IsProbabilityMeasure (gaussianReal _ _);infer_instance⟩

lemma actual_vector_observation_independent_gaussian_residual_product_derives_the_conditional_joint
    (nu : Measure (I → ℝ)) [IsProbabilityMeasure nu]
    (meanResidual : ℝ) (w : I → ℝ) (varianceResidual : ℝ≥0) :
    (nu.prod (gaussianReal meanResidual varianceResidual)).map
        (fun pair : (I → ℝ) × ℝ => (pair.1,pair.2+w ⬝ᵥ pair.1)) =
      nu ⊗ₘ conditionalKernel meanResidual w varianceResidual := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest (by fun_prop)]
  change (∫⁻ pair,test (pair.1,pair.2+w ⬝ᵥ pair.1) ∂nu.prod (gaussianReal meanResidual varianceResidual))=_
  have hmtest : Measurable (fun pair : (I → ℝ) × ℝ => test (pair.1,pair.2+w ⬝ᵥ pair.1)) :=
    htest.comp (by fun_prop)
  rw [lintegral_prod _ hmtest.aemeasurable,Measure.lintegral_compProd htest]
  apply lintegral_congr
  intro y
  have ht : Measurable (fun z => test (y,z)) := htest.comp (measurable_const.prodMk measurable_id)
  have hm := gaussianReal_map_add_const (μ:=meanResidual) (v:=varianceResidual) (w ⬝ᵥ y)
  change (∫⁻ z,test (y,z+w ⬝ᵥ y) ∂gaussianReal meanResidual varianceResidual)=
    ∫⁻ z,test (y,z) ∂gaussianReal (meanResidual+w ⬝ᵥ y) varianceResidual
  rw [← hm,lintegral_map ht (by fun_prop)]

theorem actual_arbitrary_finite_joint_gaussian_has_the_true_schur_conditional_kernel
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y)) :
    let w := (observationCovariance P Y)⁻¹ *ᵥ crossCovariance P Y Z
    P.map (fun o => (Y o,Z o)) = (P.map Y) ⊗ₘ conditionalKernel
      ((∫ o,Z o ∂P)-∑ i,w i*(∫ o,Y o i ∂P)) w
      (Var[Z;P]-w ⬝ᵥ crossCovariance P Y Z).toNNReal := by
  intro w
  have hs : observationCovariance P Y *ᵥ w=crossCovariance P Y Z :=
    actual_inverse_covariance_coefficients_solve_the_true_covariance_system P Y Z hunit
  have hg := actual_finite_gaussian_observations_and_regression_residual_are_jointly_gaussian P Y Z hYZ w
  haveI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYZ.fst.aemeasurable).2 inferInstance
  have hi := actual_finite_gaussian_regression_residual_is_independent_of_the_whole_observation_vector P Y Z hYZ w hs
  have hp := hi.map_prod_eq_prod_map_map hYZ.fst.aemeasurable hg.snd.aemeasurable
  have hl := hg.snd.map_eq_gaussianReal
  rw [(actual_finite_regression_mean_and_variance_are_the_true_schur_expressions P Y Z hYZ w hs).1,
    (actual_finite_regression_mean_and_variance_are_the_true_schur_expressions P Y Z hYZ w hs).2] at hl
  have he : (P.map (fun o => (Y o,residual Y Z w o))).map
      (fun pair : (I → ℝ) × ℝ => (pair.1,pair.2+w ⬝ᵥ pair.1)) =
      P.map (fun o => (Y o,Z o)) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hg.aemeasurable]
    congr 1
    funext o
    simp [residual,dotProduct]
  rw [← he,hp,hl]
  exact actual_vector_observation_independent_gaussian_residual_product_derives_the_conditional_joint _ _ _ _

end SafeLearning.CompleteModulesGaussianRegressionFinite
