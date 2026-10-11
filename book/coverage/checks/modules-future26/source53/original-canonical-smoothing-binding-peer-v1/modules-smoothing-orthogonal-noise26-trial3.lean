import SafeLearning.CompleteModulesGaussianMatrixLaws
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
namespace SafeLearning.CompleteModulesSmoothingOrthogonalNoise26

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def orthogonalResidual (unit : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ unit).smulRight unit

theorem actual_standard_gaussian_unit_projection_law (unit : E) (hu : ‖unit‖ = 1) :
    (stdGaussian E).map (fun z : E => ⟪unit,z⟫) = gaussianReal 0 1 := by
  have hg := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun (innerSL ℝ unit)
  have hv : Var[fun z : E => ⟪unit,z⟫; stdGaussian E] = 1 := by
    have ht := variance_dual_stdGaussian (innerSL ℝ unit)
    simpa only [coe_innerSL_apply,innerSL_apply_norm,hu,one_pow] using ht
  have hg' : HasGaussianLaw (fun z : E => ⟪unit,z⟫) (stdGaussian E) := by
    simpa only [id_eq,innerSL_apply_apply] using hg
  rw [hg'.map_eq_gaussianReal]
  have hm : (∫ z : E, ⟪unit,z⟫ ∂stdGaussian E) = 0 := by
    simpa only [coe_innerSL_apply] using integral_strongDual_stdGaussian (innerSL ℝ unit)
  rw [hm,hv]
  norm_num

theorem actual_gaussian_projection_and_orthogonal_residual_are_independent
    (unit : E) (hu : ‖unit‖ = 1) :
    IndepFun (fun z : E => ⟪unit,z⟫) (orthogonalResidual unit) (stdGaussian E) := by
  have hg := IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)
  have hpair := hg.map_fun ((innerSL ℝ unit).prod (orthogonalResidual unit))
  have hc (a b : E) : cov[fun z : E => ⟪a,z⟫,fun z : E => ⟪b,z⟫; stdGaussian E] = ⟪a,b⟫ := by
    rw [←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,innerSL_apply_apply]
  have hnorm : ⟪unit,unit⟫ = 1 := by rw [real_inner_self_eq_norm_sq,hu];norm_num
  have hpair' : HasGaussianLaw (fun z : E => (⟪unit,z⟫,orthogonalResidual unit z)) (stdGaussian E) := by
    simpa only [id_eq,ContinuousLinearMap.prod_apply,innerSL_apply_apply] using hpair
  apply hpair'.indepFun_of_covariance_inner
  intro scalar vector
  have hi (v : E) : MemLp (fun z : E => ⟪v,z⟫) 2 (stdGaussian E) := by
    simpa only [id_eq,innerSL_apply_apply] using (hg.map_fun (innerSL ℝ v)).memLp_two
  have hr (a b : ℝ) : ⟪a,b⟫ = a*b := by
    simp only [RCLike.inner_apply,conj_trivial,mul_comm]
  simp only [hr,orthogonalResidual,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]
  change cov[fun z : E => scalar * ⟪unit,z⟫,
    fun z : E => ⟪vector,z-⟪unit,z⟫ • unit⟫; stdGaussian E] = 0
  simp only [inner_sub_right,real_inner_smul_right]
  rw [covariance_const_mul_left,covariance_fun_sub_right (hi unit) (hi vector)
    ((hi unit).mul_const ⟪vector,unit⟫),covariance_mul_const_right,hc,hc,hnorm]
  rw [real_inner_comm unit vector]
  ring

theorem actual_full_gaussian_joint_noise_decomposition (unit : E) (hu : ‖unit‖ = 1) :
    (stdGaussian E).map (fun z : E => (⟪unit,z⟫,orthogonalResidual unit z)) =
      (gaussianReal 0 1).prod ((stdGaussian E).map (orthogonalResidual unit)) ∧
    (∀ z : E, ⟪unit,z⟫ • unit + orthogonalResidual unit z = z) := by
  have hi := actual_gaussian_projection_and_orthogonal_residual_are_independent unit hu
  have hj := hi.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  rw [actual_standard_gaussian_unit_projection_law unit hu] at hj
  refine ⟨hj,?_⟩
  intro z
  simp only [orthogonalResidual,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]
  abel

end SafeLearning.CompleteModulesSmoothingOrthogonalNoise26
