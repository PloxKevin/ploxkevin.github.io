import SafeLearning.CompleteModulesGaussianMatrixLaws
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod

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


theorem actual_bounded_probability_test_integrable
    {X : Type*} [MeasurableSpace X] (measure : Measure X) [IsProbabilityMeasure measure]
    (f : X → ℝ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    Integrable f measure := by
  have hp : Integrable (fun _ : X => (1:ℝ)) measure := integrable_const 1
  have hh := hp.bdd_mul hf.aestronglyMeasurable (ae_of_all measure (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]
    exact (hb x).2))
  simpa only [mul_one] using hh

theorem actual_bounded_gaussian_fiber_integral_decomposition
    (unit : E) (hu : ‖unit‖ = 1) (f : E → ℝ) (hf : Measurable f)
    (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Measurable (fun t : ℝ => ∫ v : E, f (t • unit + v)
      ∂((stdGaussian E).map (orthogonalResidual unit))) ∧
    (∀ t : ℝ, 0 ≤ (∫ v : E, f (t • unit + v)
      ∂((stdGaussian E).map (orthogonalResidual unit))) ∧
      (∫ v : E, f (t • unit + v)
        ∂((stdGaussian E).map (orthogonalResidual unit))) ≤ 1) ∧
    (∫ z : E, f z ∂stdGaussian E) =
      ∫ t : ℝ, (∫ v : E, f (t • unit + v)
        ∂((stdGaussian E).map (orthogonalResidual unit))) ∂gaussianReal 0 1 := by
  let residualLaw := (stdGaussian E).map (orthogonalResidual unit)
  let F : ℝ × E → ℝ := fun p => f (p.1 • unit + p.2)
  have hF : Measurable F := hf.comp (by fun_prop)
  have hFb : ∀ p, 0 ≤ F p ∧ F p ≤ 1 := fun p => hb _
  have hi := actual_bounded_probability_test_integrable
    ((gaussianReal 0 1).prod residualLaw) F hF hFb
  have hm : Measurable (fun t : ℝ => ∫ v : E, f (t • unit + v) ∂residualLaw) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨hm,?_,?_⟩
  · intro t
    have hft : Measurable (fun v : E => f (t • unit + v)) := hf.comp (by fun_prop)
    have hit := actual_bounded_probability_test_integrable residualLaw _ hft (fun v => hb _)
    refine ⟨integral_nonneg (fun v => (hb _).1),?_⟩
    have hx := integral_mono hit (integrable_const (1:ℝ)) (fun v => (hb _).2)
    simpa using hx
  · have hj := actual_full_gaussian_joint_noise_decomposition unit hu
    calc
      (∫ z : E, f z ∂stdGaussian E) =
          ∫ z : E, F (⟪unit,z⟫,orthogonalResidual unit z) ∂stdGaussian E := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by change f z=f (⟪unit,z⟫ • unit + orthogonalResidual unit z);rw [hj.2 z])
      _ = ∫ p : ℝ × E, F p ∂((stdGaussian E).map
          (fun z : E => (⟪unit,z⟫,orthogonalResidual unit z))) :=
        (integral_map_of_stronglyMeasurable (by fun_prop) hF.stronglyMeasurable).symm
      _ = ∫ p : ℝ × E, F p ∂((gaussianReal 0 1).prod residualLaw) := by rw [hj.1]
      _ = ∫ t : ℝ, (∫ v : E, f (t • unit + v) ∂residualLaw) ∂gaussianReal 0 1 :=
        integral_prod F hi


theorem actual_shifted_gaussian_fiber_integral
    (unit : E) (hu : ‖unit‖ = 1) (f : E → ℝ) (hf : Measurable f)
    (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (shift : ℝ) :
    (∫ z : E, f (shift • unit + z) ∂stdGaussian E) =
      ∫ t : ℝ, (∫ v : E, f (t • unit + v)
        ∂((stdGaussian E).map (orthogonalResidual unit))) ∂gaussianReal shift 1 := by
  have hg : Measurable (fun z : E => f (shift • unit + z)) := hf.comp (by fun_prop)
  have hd := actual_bounded_gaussian_fiber_integral_decomposition unit hu
    (fun z : E => f (shift • unit + z)) hg (fun z => hb _)
  have hm := (actual_bounded_gaussian_fiber_integral_decomposition unit hu f hf hb).1
  have hmap : (gaussianReal 0 1).map (fun t : ℝ => t+shift) = gaussianReal shift 1 := by
    simpa using (gaussianReal_map_add_const (μ:=0) (v:=1) shift)
  have hi := integral_map_of_stronglyMeasurable (μ:=gaussianReal 0 1)
    (show Measurable (fun t : ℝ => t+shift) by fun_prop) hm.stronglyMeasurable
  rw [hmap] at hi
  rw [hd.2.2,hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      congr 1
      rw [add_smul]
      abel))

end SafeLearning.CompleteModulesSmoothingOrthogonalNoise26
