import SafeLearning.CompleteAppliedConcentration
import Mathlib.Probability.Kernel.CondDistrib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConditionalLaw
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem conditional_hoeffding_any_space {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ mΩ inferInstance X) (R : ℝ≥0)
    (hb : ∀ᵐ omega ∂μ,X omega ∈ Set.Icc (-(R:ℝ)) R)
    (hz : μ[X | m]=ᵐ[μ] 0) :
    (∀ lambda : ℝ,Integrable (fun omega => Real.exp (lambda*X omega)) μ) ∧
    (∀ lambda : ℝ,∀ᵐ omega ∂μ,
      (μ[fun w => Real.exp (lambda*X w) | m]) omega ≤
        Real.exp (lambda^2*(R:ℝ)^2/2)) := by
  letI : MeasurableSpace Ω := mΩ
  let K : @Kernel Ω ℝ m inferInstance :=
    @condDistrib Ω Ω ℝ inferInstance inferInstance inferInstance mΩ m X id μ inferInstance
  have hcond : @Measurable Ω Ω mΩ m id := measurable_id'' hm
  have hi : Integrable X μ := (memLp_of_bounded hb hX.aestronglyMeasurable 2).integrable (by norm_num)
  have hcomp : K ∘ₘ μ.trim hm = μ.map X := by
    dsimp only [K]
    rw [trim_eq_map]
    exact condDistrib_comp_map (mβ := m) (@Measurable.aemeasurable Ω Ω mΩ m id μ hcond) hX.aemeasurable
  have hblaw : ∀ᵐ y ∂μ.map X,y ∈ Set.Icc (-(R:ℝ)) R :=
    (ae_map_iff hX.aemeasurable measurableSet_Icc).mpr hb
  have hkb : ∀ᵐ omega ∂μ,∀ᵐ y ∂K omega,y ∈ Set.Icc (-(R:ℝ)) R := by
    apply ae_of_ae_trim hm
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact hblaw
  have hmean : μ[X | m]=ᵐ[μ] fun omega => ∫ y,y ∂K omega := by
    simpa only [MeasurableSpace.comap_id,Function.id_comp,Function.comp_id,id_eq,K] using
      condExp_ae_eq_integral_condDistrib (mβ := m) hcond hX.aemeasurable
        stronglyMeasurable_id hi
  have hkzero : ∀ᵐ omega ∂μ,(∫ y,y ∂K omega)=0 := by
    filter_upwards [hmean,hz] with omega he hzero
    exact he.symm.trans hzero
  have hex (lambda : ℝ) : Integrable (fun omega => Real.exp (lambda*X omega)) μ :=
    integrable_exp_mul_of_mem_Icc hX.aemeasurable hb
  refine ⟨hex,?_⟩
  intro lambda
  have hce : μ[fun w => Real.exp (lambda*X w) | m]=ᵐ[μ]
      fun omega => ∫ y,Real.exp (lambda*y) ∂K omega := by
    simpa only [MeasurableSpace.comap_id,id_eq,K,Pi.mul_apply] using
      condExp_ae_eq_integral_condDistrib (mβ := m) hcond hX.aemeasurable
        ((measurable_const.mul measurable_id).exp.stronglyMeasurable) (hex lambda)
  filter_upwards [hce,hkb,hkzero] with omega he hbound hzero
  rw [he]
  have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (measurable_id.aemeasurable (μ := K omega)) hbound hzero
  have hparameter : (‖(R:ℝ)-(-(R:ℝ))‖₊/2)^2=R^2 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow,NNReal.coe_div,coe_nnnorm,NNReal.coe_ofNat]
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [R.property])]
    ring
  rw [hparameter] at hh
  simpa [mgf,mul_comm] using hh.mgf_le lambda

end SafeLearning.CompleteAppliedConditionalLaw
