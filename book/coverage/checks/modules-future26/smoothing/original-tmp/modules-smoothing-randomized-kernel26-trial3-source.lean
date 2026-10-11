import SafeLearning.CompleteAppliedGaussianQuantile
import SafeLearning.CompleteFoundationsNormDuality
import SafeLearning.CompleteModulesGaussianMatrixLaws
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesSmoothingNeymanPearson26

variable {E : Type*} [MeasurableSpace E]

theorem actual_density_test_transfer_from_low_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, q z ≤ cutoff * p z)
    (houtside : ∀ z ∉ S, cutoff * p z ≤ q z)
    (hmass : (∫ z in S, p z ∂base) ≤ ∫ z, h z * p z ∂base) :
    (∫ z in S, q z ∂base) ≤ ∫ z, h z * q z ∂base := by
  have hpoint (z : E) :
      cutoff * (h z * p z - S.indicator p z) ≤ h z * q z - S.indicator q z := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (cutoff*p z-q z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      have hn := mul_nonneg ((hh z).1) (sub_nonneg.mpr (houtside z hz))
      nlinarith
  have hi := integral_mono ((hhp.sub (hp.indicator hS)).const_mul cutoff)
    (hhq.sub (hq.indicator hS)) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_density_test_transfer_from_high_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, cutoff * p z ≤ q z)
    (houtside : ∀ z ∉ S, q z ≤ cutoff * p z)
    (hmass : (∫ z, h z * p z ∂base) ≤ ∫ z in S, p z ∂base) :
    (∫ z, h z * q z ∂base) ≤ ∫ z in S, q z ∂base := by
  have hpoint (z : E) :
      h z * q z - S.indicator q z ≤ cutoff * (h z * p z - S.indicator p z) := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (q z-cutoff*p z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      have hn := mul_nonneg ((hh z).1) (sub_nonneg.mpr (houtside z hz))
      nlinarith
  have hi := integral_mono (hhq.sub (hq.indicator hS))
    ((hhp.sub (hp.indicator hS)).const_mul cutoff) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_bounded_measurable_test_has_integrable_density_products
    (base : Measure E) (p h : E → ℝ) (hp : Integrable p base)
    (hm : Measurable h) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1) :
    Integrable (fun z => h z * p z) base := by
  apply hp.bdd_mul hm.aestronglyMeasurable
  exact ae_of_all base (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hh z).1]
    exact (hh z).2)


open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile

theorem actual_scalar_shifted_gaussian_density_ratio (shift point : ℝ) :
    gaussianPDFReal shift 1 point = gaussianPDFReal 0 1 point *
      Real.exp (shift*point-shift^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem actual_scalar_gaussian_low_halfspace_is_a_likelihood_region
    (shift threshold : ℝ) (hshift : 0 ≤ shift) :
    (∀ point ≤ threshold, gaussianPDFReal shift 1 point ≤
      Real.exp (shift*threshold-shift^2/2) * gaussianPDFReal 0 1 point) ∧
    (∀ point ≥ threshold, Real.exp (shift*threshold-shift^2/2) *
      gaussianPDFReal 0 1 point ≤ gaussianPDFReal shift 1 point) := by
  constructor <;> intro point hp
  · rw [actual_scalar_shifted_gaussian_density_ratio shift point]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [actual_scalar_shifted_gaussian_density_ratio shift point]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem actual_shifted_scalar_gaussian_halfspace_mass (shift threshold : ℝ) :
    (gaussianReal shift 1).real (Iic threshold) = standardCDF (threshold-shift) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => x+shift) = gaussianReal shift 1 := by
    simpa using (gaussianReal_map_add_const (μ:=0) (v:=1) shift)
  have hh := map_measureReal_apply (μ:=gaussianReal 0 1)
    (show Measurable (fun x : ℝ => x+shift) by fun_prop) (s:=Iic threshold) measurableSet_Iic
  rw [hmap] at hh
  have hs : (fun x : ℝ => x+shift) ⁻¹' Iic threshold = Iic (threshold-shift) := by
    ext x
    simp only [mem_preimage,mem_Iic]
    constructor <;> intro hx <;> linarith
  simpa only [hs,standardCDF] using hh

theorem actual_scalar_gaussian_transfer_for_every_bounded_measurable_test
    (h : ℝ → ℝ) (hm : Measurable h) (hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (shift threshold : ℝ) (hshift : 0 ≤ shift)
    (hbase : standardCDF threshold ≤ ∫ z, h z ∂gaussianReal 0 1) :
    standardCDF (threshold-shift) ≤ ∫ z, h z ∂gaussianReal shift 1 := by
  have hp := integrable_gaussianPDFReal 0 1
  have hq := integrable_gaussianPDFReal shift 1
  have hhp := actual_bounded_measurable_test_has_integrable_density_products volume _ h hp hm hb
  have hhq := actual_bounded_measurable_test_has_integrable_density_products volume _ h hq hm hb
  have hi := actual_scalar_gaussian_low_halfspace_is_a_likelihood_region shift threshold hshift
  have hx (mean : ℝ) : (gaussianReal mean 1).real (Iic threshold) =
      ∫ z in Iic threshold, gaussianPDFReal mean 1 z := by
    rw [measureReal_def,gaussianReal_apply_eq_integral _ (by norm_num),ENNReal.toReal_ofReal]
    exact integral_nonneg (fun z => gaussianPDFReal_nonneg _ _ _)
  have hf (mean : ℝ) : (∫ z, h z ∂gaussianReal mean 1) =
      ∫ z, h z * gaussianPDFReal mean 1 z := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
    simp only [smul_eq_mul,mul_comm]
  have hbase' : (∫ z in Iic threshold, gaussianPDFReal 0 1 z) ≤
      ∫ z, h z * gaussianPDFReal 0 1 z := by
    rw [←hx 0,←hf 0]
    exact hbase
  have ht := actual_density_test_transfer_from_low_likelihood_region volume
    (gaussianPDFReal 0 1) (gaussianPDFReal shift 1) h (Iic threshold)
    measurableSet_Iic hp hq hhp hhq hb (Real.exp (shift*threshold-shift^2/2))
    (Real.exp_pos _).le (fun z hz => hi.1 z hz)
    (fun z hz => hi.2 z (le_of_lt (lt_of_not_ge hz))) hbase'
  rw [←hx shift,actual_shifted_scalar_gaussian_halfspace_mass,←hf shift] at ht
  exact ht

theorem actual_scalar_ideal_majority_for_every_strict_standardized_shift
    (h : ℝ → ℝ) (hm : Measurable h) (hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (shift : ℝ) (hshift : 0 ≤ shift) (hradius : shift < 2)
    (hbase : standardCDF 2 ≤ ∫ z, h z ∂gaussianReal 0 1) :
    (1/2:ℝ) < ∫ z, h z ∂gaussianReal shift 1 := by
  have htransfer := actual_scalar_gaussian_transfer_for_every_bounded_measurable_test
    h hm hb shift 2 hshift hbase
  have hhalf : (1/2:ℝ) < standardCDF (2-shift) := by
    rw [←actual_standard_gaussian_symmetry_and_half_mass]
    apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
    linarith
  exact hhalf.trans_le htransfer


variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]

def scalarClassMass (classifier : ℝ → Y) (shift : ℝ) (label : Y) : ℝ :=
  (gaussianReal shift 1).real (classifier ⁻¹' {label})

def scalarIdealWinner (classifier : ℝ → Y) (shift : ℝ) (label : Y) : Prop :=
  ∀ other, other ≠ label → scalarClassMass classifier shift other < scalarClassMass classifier shift label

theorem actual_scalar_ideal_classifier_retains_every_true_majority_label
    (classifier : ℝ → Y) (hf : Measurable classifier) (label : Y)
    (shift : ℝ) (hshift : 0 ≤ shift) (hradius : shift < 2)
    (hbase : standardCDF 2 ≤ scalarClassMass classifier 0 label) :
    scalarIdealWinner classifier shift label := by
  let A := classifier ⁻¹' {label}
  have hA : MeasurableSet A := hf (measurableSet_singleton label)
  let h : ℝ → ℝ := A.indicator (fun _ => 1)
  have hm : Measurable h := measurable_const.indicator hA
  have hb : ∀ z, 0 ≤ h z ∧ h z ≤ 1 := by
    intro z
    by_cases hz : z ∈ A <;> simp [h,hz]
  have hh (mean : ℝ) : (∫ z, h z ∂gaussianReal mean 1) = scalarClassMass classifier mean label := by
    simpa only [h,scalarClassMass,A,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=gaussianReal mean 1) (1:ℝ) hA)
  have hmj : (1/2:ℝ) < scalarClassMass classifier shift label := by
    rw [←hh shift]
    exact actual_scalar_ideal_majority_for_every_strict_standardized_shift h hm hb shift hshift hradius
      (by rw [hh 0]; exact hbase)
  intro other hother
  let B := classifier ⁻¹' {other}
  have hB : MeasurableSet B := hf (measurableSet_singleton other)
  have hd : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z ha hb
    exact hother (hb.symm.trans ha)
  have hu := measureReal_mono (μ:=gaussianReal shift 1)
    (s₁:=A∪B) (s₂:=univ) (subset_univ _)
  rw [measureReal_union hd hB] at hu
  have hone : (gaussianReal shift 1).real univ = 1 := by simp
  rw [hone] at hu
  change scalarClassMass classifier shift label + scalarClassMass classifier shift other ≤ 1 at hu
  linarith

theorem actual_scalar_confidence_is_over_estimation_samples
    {Omega : Type*} [MeasurableSpace Omega]
    (samples : Measure Omega) [IsProbabilityMeasure samples]
    (classifier : ℝ → Y) (hf : Measurable classifier) (selectedLabel : Omega → Y)
    (confidenceEvent : Set Omega) (hconfidence : (999/1000:ℝ) ≤ samples.real confidenceEvent)
    (hvalid : ∀ omega ∈ confidenceEvent,
      standardCDF 2 ≤ scalarClassMass classifier 0 (selectedLabel omega)) :
    (999/1000:ℝ) ≤ samples.real {omega | ∀ shift : ℝ,
      0 ≤ shift → shift < 2 → scalarIdealWinner classifier shift (selectedLabel omega)} := by
  apply hconfidence.trans
  apply measureReal_mono (h₂:=by finiteness)
  intro omega homega shift hnonnegative hstrict
  exact actual_scalar_ideal_classifier_retains_every_true_majority_label classifier hf
    (selectedLabel omega) shift hnonnegative hstrict (hvalid omega homega)

theorem actual_scalar_boundary_halfspace_has_no_strict_majority :
    (gaussianReal 2 1).real (Iic 2) = 1/2 ∧
    (gaussianReal 2 1).real (Iic 2)ᶜ = 1/2 ∧
    ¬ ((gaussianReal 2 1).real (Iic 2)ᶜ < (gaussianReal 2 1).real (Iic 2)) := by
  have hh : (gaussianReal 2 1).real (Iic 2) = 1/2 := by
    rw [actual_shifted_scalar_gaussian_halfspace_mass]
    norm_num only [sub_self]
    exact actual_standard_gaussian_symmetry_and_half_mass
  have hc := measureReal_add_measureReal_compl (μ:=gaussianReal 2 1)
    (s:=Iic 2) measurableSet_Iic
  rw [hh] at hc
  have hone : (gaussianReal 2 1).real univ = 1 := by simp
  rw [hone] at hc
  refine ⟨hh, by linarith, ?_⟩
  rw [hh]
  linarith

end SafeLearning.CompleteModulesSmoothingNeymanPearson26



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


open SafeLearning.CompleteModulesSmoothingNeymanPearson26
open SafeLearning.CompleteAppliedGaussianCDF SafeLearning.CompleteAppliedGaussianQuantile

theorem actual_nd_gaussian_event_transfer_for_every_bounded_measurable_test
    (unit : E) (hu : ‖unit‖ = 1) (f : E → ℝ) (hf : Measurable f)
    (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (shift threshold : ℝ) (hs : 0 ≤ shift)
    (hbase : standardCDF threshold ≤ ∫ z : E, f z ∂stdGaussian E) :
    standardCDF (threshold-shift) ≤ ∫ z : E, f (shift • unit+z) ∂stdGaussian E := by
  have hd := actual_bounded_gaussian_fiber_integral_decomposition unit hu f hf hb
  rw [actual_shifted_gaussian_fiber_integral unit hu f hf hb shift]
  apply actual_scalar_gaussian_transfer_for_every_bounded_measurable_test
    _ hd.1 hd.2.1 shift threshold hs
  rw [←hd.2.2]
  exact hbase

theorem actual_nd_true_majority_inside_every_strict_direction
    (unit : E) (hu : ‖unit‖ = 1) (f : E → ℝ) (hf : Measurable f)
    (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (shift : ℝ) (hs : 0 ≤ shift) (hr : shift < 2)
    (hbase : standardCDF 2 ≤ ∫ z : E, f z ∂stdGaussian E) :
    (1/2:ℝ) < ∫ z : E, f (shift • unit+z) ∂stdGaussian E := by
  have ht := actual_nd_gaussian_event_transfer_for_every_bounded_measurable_test
    unit hu f hf hb shift 2 hs hbase
  have hh : (1/2:ℝ) < standardCDF (2-shift) := by
    rw [←actual_standard_gaussian_symmetry_and_half_mass]
    apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
    linarith
  exact hh.trans_le ht


theorem actual_scaled_nd_gaussian_majority_for_every_strict_euclidean_ball
    (f : E → ℝ) (hf : Measurable f) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1)
    (location perturbation : E) (sigma : ℝ) (hsigma : 0 < sigma)
    (hball : ‖perturbation‖ < 2*sigma)
    (hbase : standardCDF 2 ≤ ∫ z : E, f (location+sigma • z) ∂stdGaussian E) :
    (1/2:ℝ) < ∫ z : E, f (location+perturbation+sigma • z) ∂stdGaussian E := by
  let d : E := sigma⁻¹ • perturbation
  let g : E → ℝ := fun z => f (location+sigma • z)
  have hg : Measurable g := hf.comp (by fun_prop)
  have hgb : ∀ z, 0 ≤ g z ∧ g z ≤ 1 := fun z => hb _
  have ht : (∫ z : E, f (location+perturbation+sigma • z) ∂stdGaussian E) =
      ∫ z : E, g (d+z) ∂stdGaussian E := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      change f (location+perturbation+sigma • z)=f (location+sigma • (sigma⁻¹ • perturbation+z))
      rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt hsigma),one_smul]
      rw [add_assoc])
  rw [ht]
  by_cases hd : d=0
  · simp only [hd,zero_add]
    have hh : (1/2:ℝ) < standardCDF 2 := by
      rw [←actual_standard_gaussian_symmetry_and_half_mass]
      apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
      norm_num
    exact hh.trans_le hbase
  · have hdn : ‖d‖ = ‖perturbation‖/sigma := by
      dsimp [d]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hsigma]
      rw [div_eq_mul_inv,mul_comm]
    have hdn0 : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    let unit : E := ‖d‖⁻¹ • d
    have hu : ‖unit‖=1 := by
      dsimp [unit]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg d),inv_mul_cancel₀ hdn0]
    have hdu : ‖d‖ • unit = d := by
      dsimp [unit]
      rw [smul_smul,mul_inv_cancel₀ hdn0,one_smul]
    have hr : ‖d‖<2 := by
      rw [hdn]
      exact (div_lt_iff₀ hsigma).mpr hball
    have hx := actual_nd_true_majority_inside_every_strict_direction unit hu g hg hgb
      ‖d‖ (norm_nonneg d) hr hbase
    rw [hdu] at hx
    exact hx


variable {Label : Type*} [MeasurableSpace Label] [MeasurableSingletonClass Label]

def ndClassMass (classifier : E → Label) (location : E) (sigma : ℝ) (label : Label) : ℝ :=
  (stdGaussian E).real ((fun z : E => classifier (location+sigma • z)) ⁻¹' {label})

def ndIdealWinner (classifier : E → Label) (location : E) (sigma : ℝ) (label : Label) : Prop :=
  ∀ other, other ≠ label → ndClassMass classifier location sigma other <
    ndClassMass classifier location sigma label

theorem actual_nd_class_mass_is_the_genuine_gaussian_indicator_integral
    (classifier : E → Label) (hc : Measurable classifier) (location : E) (sigma : ℝ)
    (label : Label) :
    (∫ z : E, (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ))
      (location+sigma • z) ∂stdGaussian E) = ndClassMass classifier location sigma label := by
  let A : Set E := (fun z : E => classifier (location+sigma • z)) ⁻¹' {label}
  have hA : MeasurableSet A := (hc.comp (by fun_prop)) (measurableSet_singleton label)
  have he : (fun z : E => (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ))
      (location+sigma • z)) = A.indicator (fun _ => (1:ℝ)) := by
    funext z
    rfl
  rw [he]
  simpa only [ndClassMass,A,smul_eq_mul,mul_one] using
    (integral_indicator_const (μ:=stdGaussian E) (1:ℝ) hA)

theorem actual_nd_smoothed_classifier_retains_every_label_inside_true_euclidean_radius
    (classifier : E → Label) (hc : Measurable classifier) (location perturbation : E)
    (sigma : ℝ) (hsigma : 0 < sigma) (label : Label)
    (hball : ‖perturbation‖ < 2*sigma)
    (hbase : standardCDF 2 ≤ ndClassMass classifier location sigma label) :
    ndIdealWinner classifier (location+perturbation) sigma label := by
  let A := classifier ⁻¹' {label}
  have hA : MeasurableSet A := hc (measurableSet_singleton label)
  let f : E → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1 := by
    intro z
    by_cases hz : z ∈ A <;> simp [f,hz]
  have hmajor : (1/2:ℝ) < ndClassMass classifier (location+perturbation) sigma label := by
    have hm := actual_scaled_nd_gaussian_majority_for_every_strict_euclidean_ball
      f hf hb location perturbation sigma hsigma hball
      (by rw [actual_nd_class_mass_is_the_genuine_gaussian_indicator_integral classifier hc];exact hbase)
    rw [actual_nd_class_mass_is_the_genuine_gaussian_indicator_integral classifier hc] at hm
    exact hm
  intro other hother
  let U : Set E := (fun z : E => classifier (location+perturbation+sigma • z)) ⁻¹' {label}
  let V : Set E := (fun z : E => classifier (location+perturbation+sigma • z)) ⁻¹' {other}
  have hV : MeasurableSet V := (hc.comp (by fun_prop)) (measurableSet_singleton other)
  have hd : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hu hv
    exact hother (hv.symm.trans hu)
  have hsum := measureReal_mono (μ:=stdGaussian E) (s₁:=U∪V) (s₂:=univ) (subset_univ _)
  rw [measureReal_union hd hV] at hsum
  have hone : (stdGaussian E).real univ=1 := by simp
  rw [hone] at hsum
  change ndClassMass classifier (location+perturbation) sigma label+
    ndClassMass classifier (location+perturbation) sigma other ≤ 1 at hsum
  linarith

theorem actual_nd_confidence_is_a_measurable_sampling_event_with_uniform_ideal_robustness
    {Omega : Type*} [MeasurableSpace Omega] (samples : Measure Omega) [IsProbabilityMeasure samples]
    (classifier : E → Label) (hc : Measurable classifier) (location : E)
    (sigma : ℝ) (hsigma : 0 < sigma) (selectedLabel : Omega → Label)
    (confidenceEvent : Set Omega) (hC : MeasurableSet confidenceEvent)
    (hconfidence : (999/1000:ℝ) ≤ samples.real confidenceEvent)
    (hvalid : ∀ omega ∈ confidenceEvent,
      standardCDF 2 ≤ ndClassMass classifier location sigma (selectedLabel omega)) :
    ∃ good : Set Omega, MeasurableSet good ∧ (999/1000:ℝ) ≤ samples.real good ∧
      ∀ omega ∈ good, ∀ perturbation : E, ‖perturbation‖ < 2*sigma →
        ndIdealWinner classifier (location+perturbation) sigma (selectedLabel omega) := by
  refine ⟨confidenceEvent,hC,hconfidence,?_⟩
  intro omega homega perturbation hball
  exact actual_nd_smoothed_classifier_retains_every_label_inside_true_euclidean_radius
    classifier hc location perturbation sigma hsigma (selectedLabel omega) hball (hvalid omega homega)

theorem actual_literal_half_sigma_has_true_radius_one_for_the_ideal_classifier
    (classifier : E → Label) (hc : Measurable classifier) (location : E) (label : Label)
    (hbase : standardCDF 2 ≤ ndClassMass classifier location (1/2) label) :
    ∀ perturbation : E, ‖perturbation‖<1 →
      ndIdealWinner classifier (location+perturbation) (1/2) label := by
  intro perturbation hball
  apply actual_nd_smoothed_classifier_retains_every_label_inside_true_euclidean_radius
    classifier hc location perturbation (1/2) (by norm_num) label _ hbase
  norm_num
  exact hball

end SafeLearning.CompleteModulesSmoothingOrthogonalNoise26

namespace SafeLearning.CompleteModulesSmoothingNumeric26
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianGeneralIntegral CompleteFoundationsNormDuality

def trueGaussianQuantile (probability : ℝ) : ℝ :=
  sInf {point : ℝ | probability ≤ standardCDF point}

theorem actual_true_quantile_at_every_cdf_value (point : ℝ) :
    trueGaussianQuantile (standardCDF point) = point ∧
    (∀ other, standardCDF point ≤ standardCDF other ↔ point ≤ other) := by
  have hm := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hs : {other : ℝ | standardCDF point ≤ standardCDF other} = Ici point := by
    ext other
    simpa using hm.le_iff_le
  exact ⟨by rw [trueGaussianQuantile, hs, csInf_Ici], fun other => hm.le_iff_le⟩

theorem actual_literal_gaussian_inverse_and_radii :
    trueGaussianQuantile (standardCDF 2) = 2 ∧
    standardCDF 0 = 1/2 ∧ trueGaussianQuantile (1/2) = 0 ∧
    (1/2 : ℝ) * trueGaussianQuantile (standardCDF 2) = 1 ∧
    (1/2 : ℝ) * trueGaussianQuantile (1/2) = 0 := by
  have htwo := (actual_true_quantile_at_every_cdf_value 2).1
  have hzero := (actual_true_quantile_at_every_cdf_value 0).1
  rw [actual_standard_gaussian_symmetry_and_half_mass] at hzero
  exact ⟨htwo,actual_standard_gaussian_symmetry_and_half_mass,hzero,
    by rw [htwo]; norm_num,by rw [hzero]; norm_num⟩

theorem actual_phi_two_nine_decimal_rounding :
    (97724986804/100000000000 : ℝ) < standardCDF 2 ∧
    standardCDF 2 < (97724986806/100000000000 : ℝ) ∧
    |standardCDF 2 - (977249868/1000000000 : ℝ)| < 1/2000000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have hi := actual_gaussian_exponential_integral_uniform_rational_error
    2 (by norm_num)
  have hp : (1196288013322/1000000000000 : ℝ) < actualPolynomialIntegral 2 ∧
      actualPolynomialIntegral 2 < (1196288013323/1000000000000 : ℝ) := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at hi
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · rw [abs_lt]; constructor <;> nlinarith

def certifyRadius (sigma lower : ℝ) : Option ℝ :=
  if (1/2 : ℝ) < lower then some (sigma * trueGaussianQuantile lower) else none

theorem actual_literal_certify_and_abstention :
    certifyRadius (1/2) (standardCDF 2) = some 1 ∧
    certifyRadius (1/2) (1/2) = none ∧
    ¬ ∃ radius : ℝ, 0 < radius ∧ certifyRadius (1/2) (1/2) = some radius := by
  have hp : (1/2 : ℝ) < standardCDF 2 := by
    rw [← actual_standard_gaussian_symmetry_and_half_mass]
    exact actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
      (by norm_num : (0:ℝ)<2)
  refine ⟨?_, ?_, ?_⟩
  · rw [certifyRadius, if_pos hp, actual_literal_gaussian_inverse_and_radii.2.2.2.1]
  · norm_num [certifyRadius]
  · norm_num [certifyRadius]

theorem actual_dimension_one_hundred_norm_bound (delta : Fin 100 → ℝ) :
    l2Norm delta ≤ 10 * ‖delta‖ := by
  have hb := actual_infinity_ball_in_euclidean_ball delta ‖delta‖ (norm_nonneg _) le_rfl
  norm_num at hb
  exact hb

theorem actual_strict_infinity_radius_implies_strict_euclidean_radius
    (delta : Fin 100 → ℝ) (hdelta : ‖delta‖ < (1/10:ℝ)) :
    l2Norm delta < 1 := by
  have hb := actual_dimension_one_hundred_norm_bound delta
  linarith

theorem actual_boundary_constant_vector_is_excluded :
    ‖(fun _ : Fin 100 => (1/10:ℝ))‖ = 1/10 ∧
    l2Norm (fun _ : Fin 100 => (1/10:ℝ)) = 1 ∧
    ¬ l2Norm (fun _ : Fin 100 => (1/10:ℝ)) < 1 := by
  have he := actual_constant_vector_attains_dimension_conversion
    (n:=Fin 100) (1/10:ℝ) (by norm_num)
  norm_num at he
  exact ⟨by simp,he,by rw [he]; norm_num⟩

end SafeLearning.CompleteModulesSmoothingNumeric26


namespace SafeLearning.CompleteModulesSmoothingOrthogonalNoise26
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
open CompleteFoundationsNormDuality CompleteModulesSmoothingNumeric26
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem actual_sigma_scaled_gaussian_has_the_true_sigma_squared_unit_projection
    (unit : E) (hu : ‖unit‖=1) (sigma : ℝ) :
    (stdGaussian E).map (fun z : E => ⟪unit,sigma • z⟫) =
      gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)) := by
  have hproj := actual_standard_gaussian_unit_projection_law unit hu
  calc
    _ = ((stdGaussian E).map (fun z : E => ⟪unit,z⟫)).map (fun t : ℝ => sigma*t) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext z
      simp [real_inner_smul_right]
    _ = (gaussianReal 0 1).map (fun t : ℝ => sigma*t) := by rw [hproj]
    _ = gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)) := by
      simpa using (gaussianReal_map_const_mul (μ:=0) (v:=1) sigma)

theorem actual_every_unit_gaussian_projection_halfspace_mass
    (unit : E) (hu : ‖unit‖=1) (threshold : ℝ) :
    (stdGaussian E).real {z : E | ⟪unit,z⟫ ≤ threshold} = standardCDF threshold := by
  have hh := map_measureReal_apply (μ:=stdGaussian E)
    (f:=fun z : E => ⟪unit,z⟫) (by fun_prop) (s:=Iic threshold) measurableSet_Iic
  rw [actual_standard_gaussian_unit_projection_law unit hu] at hh
  exact hh.symm

theorem actual_true_boundary_halfspace_has_base_phi_two_and_perturbed_tie
    (unit : E) (hu : ‖unit‖=1) :
    (stdGaussian E).real {z : E | ⟪unit,(1/2:ℝ) • z⟫ ≤ 1} = standardCDF 2 ∧
    (stdGaussian E).real {z : E | ⟪unit,unit+(1/2:ℝ) • z⟫ ≤ 1} = 1/2 ∧
    (stdGaussian E).real {z : E | ¬ ⟪unit,unit+(1/2:ℝ) • z⟫ ≤ 1} = 1/2 := by
  have hnorm : ⟪unit,unit⟫=(1:ℝ) := by rw [real_inner_self_eq_norm_sq,hu];norm_num
  have hb : {z : E | ⟪unit,(1/2:ℝ) • z⟫ ≤ 1}={z : E | ⟪unit,z⟫ ≤ 2} := by
    ext z
    simp only [Set.mem_setOf_eq,real_inner_smul_right]
    constructor <;> intro h <;> linarith
  have hp : {z : E | ⟪unit,unit+(1/2:ℝ) • z⟫ ≤ 1}={z : E | ⟪unit,z⟫ ≤ 0} := by
    ext z
    simp only [Set.mem_setOf_eq,inner_add_right,hnorm,real_inner_smul_right]
    constructor <;> intro h <;> linarith
  have hm : (stdGaussian E).real {z : E | ⟪unit,unit+(1/2:ℝ) • z⟫ ≤ 1}=1/2 := by
    rw [hp,actual_every_unit_gaussian_projection_halfspace_mass unit hu,
      actual_standard_gaussian_symmetry_and_half_mass]
  refine ⟨by rw [hb,actual_every_unit_gaussian_projection_halfspace_mass unit hu],hm,?_⟩
  have hset : MeasurableSet {z : E | ⟪unit,unit+(1/2:ℝ) • z⟫ ≤ 1} := by
    rw [hp]
    exact measurableSet_le (by fun_prop) measurable_const
  have hx := measureReal_compl (μ:=stdGaussian E) hset
  rw [hm,probReal_univ] at hx
  norm_num at hx
  exact hx

theorem actual_numeric_coordinate_embedding_is_the_genuine_euclidean_norm
    (delta : Fin 100 → ℝ) :
    ‖(WithLp.toLp 2 delta : EuclideanSpace ℝ (Fin 100))‖ = l2Norm delta := rfl

variable {Label : Type*} [MeasurableSpace Label] [MeasurableSingletonClass Label]

theorem actual_literal_dimension100_infinity_radius_retains_the_ideal_classifier
    (classifier : EuclideanSpace ℝ (Fin 100) → Label) (hc : Measurable classifier)
    (location : EuclideanSpace ℝ (Fin 100)) (label : Label)
    (hbase : standardCDF 2 ≤ ndClassMass classifier location (1/2) label)
    (delta : Fin 100 → ℝ) (hdelta : ‖delta‖<(1/10:ℝ)) :
    ndIdealWinner classifier (location+WithLp.toLp 2 delta) (1/2) label := by
  apply actual_literal_half_sigma_has_true_radius_one_for_the_ideal_classifier
    classifier hc location label hbase
  rw [actual_numeric_coordinate_embedding_is_the_genuine_euclidean_norm]
  exact actual_strict_infinity_radius_implies_strict_euclidean_radius delta hdelta

theorem actual_literal_dimension100_boundary_vector_has_true_unit_norm :
    ‖(WithLp.toLp 2 (fun _ : Fin 100 => (1/10:ℝ)) : EuclideanSpace ℝ (Fin 100))‖=1 ∧
    ‖(fun _ : Fin 100 => (1/10:ℝ))‖=1/10 := by
  rw [actual_numeric_coordinate_embedding_is_the_genuine_euclidean_norm]
  exact ⟨actual_boundary_constant_vector_is_excluded.2.1,
    actual_boundary_constant_vector_is_excluded.1⟩
end SafeLearning.CompleteModulesSmoothingOrthogonalNoise26


namespace SafeLearning.CompleteModulesSmoothingRandomized26
open CompleteModulesSmoothingOrthogonalNoise26 CompleteModulesSmoothingNumeric26
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {Label : Type*}
theorem actual_every_positive_cdf_threshold_has_its_true_scaled_gaussian_radius
    (f : E → ℝ) (hf : Measurable f) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1)
    (location perturbation : E) (sigma : ℝ) (hsigma : 0 < sigma)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hball : ‖perturbation‖ < threshold*sigma)
    (hbase : standardCDF threshold ≤ ∫ z : E, f (location+sigma • z) ∂stdGaussian E) :
    (1/2:ℝ) < ∫ z : E, f (location+perturbation+sigma • z) ∂stdGaussian E := by
  let d : E := sigma⁻¹ • perturbation
  let g : E → ℝ := fun z => f (location+sigma • z)
  have hg : Measurable g := hf.comp (by fun_prop)
  have hgb : ∀ z, 0 ≤ g z ∧ g z ≤ 1 := fun z => hb _
  have ht : (∫ z : E, f (location+perturbation+sigma • z) ∂stdGaussian E) =
      ∫ z : E, g (d+z) ∂stdGaussian E := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      change f (location+perturbation+sigma • z)=f (location+sigma • (sigma⁻¹ • perturbation+z))
      rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt hsigma),one_smul]
      rw [add_assoc])
  rw [ht]
  by_cases hd : d=0
  · simp only [hd,zero_add]
    have hh : (1/2:ℝ) < standardCDF threshold := by
      rw [←actual_standard_gaussian_symmetry_and_half_mass]
      apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
      exact hthreshold
    exact hh.trans_le hbase
  · have hdn : ‖d‖ = ‖perturbation‖/sigma := by
      dsimp [d]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hsigma]
      rw [div_eq_mul_inv,mul_comm]
    have hdn0 : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    let unit : E := ‖d‖⁻¹ • d
    have hu : ‖unit‖=1 := by
      dsimp [unit]
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg d),inv_mul_cancel₀ hdn0]
    have hdu : ‖d‖ • unit = d := by
      dsimp [unit]
      rw [smul_smul,mul_inv_cancel₀ hdn0,one_smul]
    have hr : ‖d‖<threshold := by
      rw [hdn]
      exact (div_lt_iff₀ hsigma).mpr hball
    have hx := actual_nd_gaussian_event_transfer_for_every_bounded_measurable_test
      unit hu g hg hgb ‖d‖ threshold (norm_nonneg d) hbase
    have hh : (1/2:ℝ) < standardCDF (threshold-‖d‖) := by
      rw [←actual_standard_gaussian_symmetry_and_half_mass]
      apply actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
      linarith
    rw [hdu] at hx
    exact hh.trans_le hx


def kernelClassMass (p : Label → E → ℝ) (location : E) (sigma : ℝ) (label : Label) : ℝ :=
  ∫ z : E, p label (location+sigma • z) ∂stdGaussian E

def kernelIdealWinner (p : Label → E → ℝ) (location : E) (sigma : ℝ) (label : Label) : Prop :=
  ∀ other, other ≠ label → kernelClassMass p location sigma other <
    kernelClassMass p location sigma label

theorem actual_normalized_class_probability_kernel_majority_is_the_true_ideal_winner
    (p : Label → E → ℝ) (hm : ∀ label, Measurable (p label))
    (hb : ∀ label x, 0 ≤ p label x ∧ p label x ≤ 1)
    (hpairs : ∀ a b, a ≠ b → ∀ x, p a x+p b x ≤ 1)
    (location : E) (sigma : ℝ) (label : Label)
    (hmajor : (1/2:ℝ) < kernelClassMass p location sigma label) :
    kernelIdealWinner p location sigma label := by
  intro other hother
  have hi (a : Label) : Integrable (fun z : E => p a (location+sigma • z)) (stdGaussian E) :=
    actual_bounded_probability_test_integrable _ _ ((hm a).comp (by fun_prop)) (fun z => hb a _)
  have hle := integral_mono ((hi label).add (hi other)) (integrable_const (1:ℝ))
    (fun z : E => hpairs label other (Ne.symm hother) (location+sigma • z))
  simp only [Pi.add_apply] at hle
  rw [integral_add (hi label) (hi other)] at hle
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hle
  change kernelClassMass p location sigma label+kernelClassMass p location sigma other ≤ 1 at hle
  linarith

theorem actual_randomized_probability_kernel_retains_every_label_at_general_quantile_radius
    (p : Label → E → ℝ) (hm : ∀ label, Measurable (p label))
    (hb : ∀ label x, 0 ≤ p label x ∧ p label x ≤ 1)
    (hpairs : ∀ a b, a ≠ b → ∀ x, p a x+p b x ≤ 1)
    (location perturbation : E) (sigma : ℝ) (hsigma : 0 < sigma)
    (label : Label) (threshold : ℝ) (hthreshold : 0 < threshold)
    (hbase : standardCDF threshold ≤ kernelClassMass p location sigma label)
    (hball : ‖perturbation‖ < sigma * trueGaussianQuantile (standardCDF threshold)) :
    kernelIdealWinner p (location+perturbation) sigma label := by
  apply actual_normalized_class_probability_kernel_majority_is_the_true_ideal_winner p hm hb hpairs
  apply actual_every_positive_cdf_threshold_has_its_true_scaled_gaussian_radius
    (p label) (hm label) (hb label) location perturbation sigma hsigma threshold hthreshold _ hbase
  rw [(actual_true_quantile_at_every_cdf_value threshold).1] at hball
  simpa only [mul_comm sigma threshold] using hball

theorem actual_randomized_kernel_confidence_is_over_samples_and_uniform_over_the_strict_ball
    {Omega : Type*} [MeasurableSpace Omega] (samples : Measure Omega) [IsProbabilityMeasure samples]
    (p : Label → E → ℝ) (hm : ∀ label, Measurable (p label))
    (hb : ∀ label x, 0 ≤ p label x ∧ p label x ≤ 1)
    (hpairs : ∀ a b, a ≠ b → ∀ x, p a x+p b x ≤ 1)
    (location : E) (sigma : ℝ) (hsigma : 0 < sigma) (selectedLabel : Omega → Label)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (confidenceEvent : Set Omega) (hC : MeasurableSet confidenceEvent)
    (hconfidence : (999/1000:ℝ) ≤ samples.real confidenceEvent)
    (hvalid : ∀ omega ∈ confidenceEvent,
      standardCDF threshold ≤ kernelClassMass p location sigma (selectedLabel omega)) :
    ∃ good : Set Omega, MeasurableSet good ∧ (999/1000:ℝ) ≤ samples.real good ∧
      ∀ omega ∈ good, ∀ perturbation : E,
        ‖perturbation‖ < sigma * trueGaussianQuantile (standardCDF threshold) →
        kernelIdealWinner p (location+perturbation) sigma (selectedLabel omega) := by
  refine ⟨confidenceEvent,hC,hconfidence,?_⟩
  intro omega homega perturbation hball
  exact actual_randomized_probability_kernel_retains_every_label_at_general_quantile_radius
    p hm hb hpairs location perturbation sigma hsigma (selectedLabel omega)
    threshold hthreshold (hvalid omega homega) hball

variable {Seed : Type*} [MeasurableSpace Seed]
variable [MeasurableSpace Label] [MeasurableSingletonClass Label]

def independentSeedClassProbability (seedLaw : Measure Seed) (classifier : E × Seed → Label)
    (label : Label) (x : E) : ℝ :=
  ∫ seed, (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ)) (x,seed) ∂seedLaw

theorem actual_independent_fixed_seed_law_produces_a_measurable_bounded_probability_kernel
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (classifier : E × Seed → Label) (hc : Measurable classifier) :
    (∀ label, Measurable (independentSeedClassProbability seedLaw classifier label)) ∧
    (∀ label x, 0 ≤ independentSeedClassProbability seedLaw classifier label x ∧
      independentSeedClassProbability seedLaw classifier label x ≤ 1) ∧
    (∀ a b, a ≠ b → ∀ x, independentSeedClassProbability seedLaw classifier a x+
      independentSeedClassProbability seedLaw classifier b x ≤ 1) := by
  have hm (label : Label) : Measurable ((classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ))) :=
    measurable_const.indicator (hc (measurableSet_singleton label))
  have hb (label : Label) (x : E × Seed) :
      0 ≤ (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ)) x ∧
      (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
    by_cases hx : x ∈ classifier ⁻¹' {label} <;> simp [hx]
  have hi (label : Label) (x : E) :
      Integrable (fun seed => (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ)) (x,seed)) seedLaw :=
    actual_bounded_probability_test_integrable _ _ ((hm label).comp (by fun_prop)) (fun seed => hb label _)
  refine ⟨?_,?_,?_⟩
  · intro label
    exact (hm label).stronglyMeasurable.integral_prod_right'.measurable
  · intro label x
    refine ⟨integral_nonneg (fun seed => (hb label (x,seed)).1),?_⟩
    have hle := integral_mono (hi label x) (integrable_const (1:ℝ)) (fun seed => (hb label (x,seed)).2)
    simpa only [independentSeedClassProbability,integral_const,probReal_univ,smul_eq_mul,one_mul] using hle
  · intro a b hab x
    have hsum (seed : Seed) :
        (classifier ⁻¹' {a}).indicator (fun _ => (1:ℝ)) (x,seed)+
        (classifier ⁻¹' {b}).indicator (fun _ => (1:ℝ)) (x,seed) ≤ 1 := by
      by_cases ha : classifier (x,seed)=a
      · have hnb : classifier (x,seed) ≠ b := fun hh => hab (ha.symm.trans hh)
        rw [Set.indicator_of_mem (show (x,seed) ∈ classifier ⁻¹' {a} from ha),
          Set.indicator_of_notMem (show (x,seed) ∉ classifier ⁻¹' {b} from hnb)]
        norm_num
      · have hx := (hb b (x,seed)).2
        simpa only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff,ha,ite_false,zero_add] using hx
    have hle := integral_mono ((hi a x).add (hi b x)) (integrable_const (1:ℝ)) hsum
    simp only [Pi.add_apply] at hle
    rw [integral_add (hi a x) (hi b x)] at hle
    simpa only [independentSeedClassProbability,integral_const,probReal_univ,smul_eq_mul,one_mul] using hle

theorem actual_independent_seed_and_gaussian_product_law_class_mass_is_the_kernel_integral
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (classifier : E × Seed → Label) (hc : Measurable classifier)
    (location : E) (sigma : ℝ) (label : Label) :
    ((stdGaussian E).prod seedLaw).real
      ((fun noise : E × Seed => classifier (location+sigma • noise.1,noise.2)) ⁻¹' {label}) =
    kernelClassMass (independentSeedClassProbability seedLaw classifier) location sigma label := by
  let F : E × Seed → ℝ := fun noise =>
    (classifier ⁻¹' {label}).indicator (fun _ => (1:ℝ)) (location+sigma • noise.1,noise.2)
  have hm : Measurable F := (measurable_const.indicator (hc (measurableSet_singleton label))).comp (by fun_prop)
  have hb : ∀ noise, 0 ≤ F noise ∧ F noise ≤ 1 := by
    intro noise
    by_cases ha : classifier (location+sigma • noise.1,noise.2)=label <;> simp [F,ha]
  have hi := actual_bounded_probability_test_integrable ((stdGaussian E).prod seedLaw) F hm hb
  have hh : F = ((fun noise : E × Seed => classifier (location+sigma • noise.1,noise.2)) ⁻¹' {label}).indicator (fun _ => (1:ℝ)) := by rfl
  have hint := integral_indicator_const (μ:=(stdGaussian E).prod seedLaw) (1:ℝ)
    ((show Measurable (fun noise : E × Seed => classifier (location+sigma • noise.1,noise.2)) from
      hc.comp (by fun_prop)) (measurableSet_singleton label))
  rw [←hh] at hint
  rw [←show (∫ noise, F noise ∂(stdGaussian E).prod seedLaw) =
      ((stdGaussian E).prod seedLaw).real ((fun noise : E × Seed => classifier (location+sigma • noise.1,noise.2)) ⁻¹' {label}) by
    simpa only [smul_eq_mul,mul_one] using hint]
  exact integral_prod F hi

theorem actual_random_base_classifier_fixed_independent_law_has_the_literal_radius_one
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (classifier : E × Seed → Label) (hc : Measurable classifier) (location : E) (label : Label)
    (hbase : standardCDF 2 ≤ kernelClassMass (independentSeedClassProbability seedLaw classifier) location (1/2) label) :
    ∀ perturbation : E, ‖perturbation‖<1 →
      kernelIdealWinner (independentSeedClassProbability seedLaw classifier) (location+perturbation) (1/2) label := by
  have hk := actual_independent_fixed_seed_law_produces_a_measurable_bounded_probability_kernel seedLaw classifier hc
  intro perturbation hball
  apply actual_randomized_probability_kernel_retains_every_label_at_general_quantile_radius
    _ hk.1 hk.2.1 hk.2.2 location perturbation (1/2) (by norm_num) label 2 (by norm_num) hbase
  rw [(actual_true_quantile_at_every_cdf_value 2).1]
  norm_num
  exact hball

end SafeLearning.CompleteModulesSmoothingRandomized26
