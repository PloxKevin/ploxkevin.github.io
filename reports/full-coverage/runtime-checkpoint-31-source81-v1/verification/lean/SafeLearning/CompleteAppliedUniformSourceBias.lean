import SafeLearning.CompleteAppliedUniformLawMGF
import Mathlib.Probability.Moments.MGFAnalytic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SafeLearning.CompleteAppliedUniformSourceBias

theorem actual_any_subgaussian_mgf_requires_zero_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0) (h : HasSubgaussianMGF X c μ) :
    (∫ omega,X omega ∂μ)=0 := by
  have hzero : (0:ℝ)∈interior (integrableExpSet X μ) := by
    rw [h.integrableExpSet_eq_univ];simp
  have hm : HasDerivAt (mgf X μ) (∫ omega,X omega ∂μ) 0 := by
    simpa using hasDerivAt_mgf (X:=X) (μ:=μ) hzero
  have hq : HasDerivAt (fun t : ℝ=>Real.exp ((c:ℝ)*t^2/2)) 0 0 := by
    simpa using ((((hasDerivAt_id (0:ℝ)).pow 2).const_mul (c:ℝ)).div_const 2).exp
  have hl : IsLocalMin (fun t : ℝ=>Real.exp ((c:ℝ)*t^2/2)-mgf X μ t) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hz : Real.exp ((c:ℝ)*(0:ℝ)^2/2)-mgf X μ 0=0 := by simp [mgf]
    change Real.exp ((c:ℝ)*(0:ℝ)^2/2)-mgf X μ 0≤Real.exp ((c:ℝ)*t^2/2)-mgf X μ t
    rw [hz]
    exact sub_nonneg.mpr (h.mgf_le t)
  have he := hl.hasDerivAt_eq_zero (hq.sub hm)
  linarith

theorem actual_source_positive_uniform_support_and_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc (0:ℝ) (1/5)) μ) :
    (∀ᵐ omega ∂μ,X omega∈Icc (0:ℝ) (1/5)) ∧
    (∫ omega,X omega ∂μ)=(1/10:ℝ) ∧ Integrable X μ := by
  have hs : ∀ᵐ omega ∂μ,X omega∈Icc (0:ℝ) (1/5) := by
    apply (hu.ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have hm : (∫ omega,X omega ∂μ)=(1/10:ℝ) := by
    rw [hu.integral_eq]
    norm_num [Real.volume_Icc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/5),integral_id]
  exact ⟨hs,hm,(memLp_of_bounded hs hu.aemeasurable.aestronglyMeasurable 2).integrable (by norm_num)⟩

theorem actual_positive_uniform_source_noise_is_not_subgaussian_at_any_parameter
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc (0:ℝ) (1/5)) μ) (c : ℝ≥0) :
    ¬HasSubgaussianMGF X c μ := by
  intro h
  have hz := actual_any_subgaussian_mgf_requires_zero_mean μ X c h
  rw [(actual_source_positive_uniform_support_and_mean μ X hu).2.1] at hz
  norm_num at hz

theorem actual_source_uniform_bias_is_explicit_and_the_centered_noise_is_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc (0:ℝ) (1/5)) μ) :
    (∀ omega,X omega=(1/10:ℝ)+(X omega-1/10)) ∧
    (∫ omega,X omega-1/10 ∂μ)=0 ∧
    (∀ᵐ omega ∂μ,X omega-1/10∈Icc (-(1/10):ℝ) (1/10)) ∧
    HasSubgaussianMGF (fun omega=>X omega-1/10) (1/100) μ := by
  obtain ⟨hs,hm,hi⟩ := actual_source_positive_uniform_support_and_mean μ X hu
  have hz : (∫ omega,X omega-1/10 ∂μ)=0 := by
    rw [integral_sub hi (integrable_const _),hm];norm_num
  have hb : ∀ᵐ omega ∂μ,X omega-1/10∈Icc (-(1/10):ℝ) (1/10) := by
    filter_upwards [hs] with omega hw
    constructor <;> linarith [hw.1,hw.2]
  refine ⟨fun omega=>by ring,hz,hb,?_⟩
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (hu.aemeasurable.sub_const (1/10:ℝ)) hb hz
  have hp : (‖(1/10:ℝ)-(-(1/10))‖₊/2)^2=(1/100:ℝ≥0) := by
    apply NNReal.coe_injective;norm_num
  rwa [hp] at h

end SafeLearning.CompleteAppliedUniformSourceBias
