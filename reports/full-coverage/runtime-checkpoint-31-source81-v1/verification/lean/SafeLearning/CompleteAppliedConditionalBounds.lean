import SafeLearning.CompleteAppliedConcentration
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConditionalBounds
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem conditional_hoeffding {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ mΩ inferInstance X) (R : ℝ≥0)
    (hb : ∀ᵐ omega ∂μ,X omega ∈ Set.Icc (-(R:ℝ)) R)
    (hz : μ[X | m]=ᵐ[μ] 0) : HasCondSubgaussianMGF m hm X (R^2) μ := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable X μ := (memLp_of_bounded hb hX.aestronglyMeasurable 2).integrable (by norm_num)
  have hzt : μ[X | m]=ᵐ[μ.trim hm] 0 :=
    (StronglyMeasurable.ae_eq_trim_iff hm stronglyMeasurable_condExp stronglyMeasurable_zero).mpr hz
  have hkernelzero : ∀ᵐ omega ∂μ.trim hm,(∫ w,X w ∂condExpKernel μ m omega)=0 := by
    filter_upwards [hzt,condExp_ae_eq_trim_integral_condExpKernel hm hi] with omega hh he
    exact he.symm.trans hh
  have hkb : ∀ᵐ omega ∂μ.trim hm,∀ᵐ w ∂condExpKernel μ m omega,
      X w ∈ Set.Icc (-(R:ℝ)) R := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim]
    exact hb
  refine ⟨?_,?_⟩
  · intro t
    rw [condExpKernel_comp_trim]
    apply Integrable.mono' (integrable_const (Real.exp (|t| * (R:ℝ))))
      ((measurable_const.mul hX).exp.aestronglyMeasurable)
    filter_upwards [hb] with omega homega
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hx : |X omega|≤R := abs_le.mpr homega
    exact (le_abs_self (t*X omega)).trans (by rw [abs_mul];gcongr)
  · filter_upwards [hkernelzero,hkb] with omega homega hbound
    have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hX.aemeasurable (μ := condExpKernel μ m omega)) hbound homega
    have hparameter : (‖(R:ℝ)-(-(R:ℝ))‖₊/2)^2=R^2 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_pow,NNReal.coe_div,coe_nnnorm,NNReal.coe_ofNat]
      rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [R.property])]
      ring
    rw [hparameter] at hh
    exact hh.mgf_le

end SafeLearning.CompleteAppliedConditionalBounds
