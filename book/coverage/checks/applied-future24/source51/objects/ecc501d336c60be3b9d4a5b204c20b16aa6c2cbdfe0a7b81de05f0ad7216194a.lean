import SafeLearning.CompleteAppliedAzuma
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedUniformBias
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology BigOperators

theorem uniform_support {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc 0 2) μ) :
    ∀ᵐ omega ∂μ, X omega ∈ Icc (0 : ℝ) 2 := by
  apply (hu.ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem uniform_mean_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc 0 2) μ) : ∫ omega, X omega ∂μ = 1 := by
  have hv : volume (Icc (0 : ℝ) 2) = 2 := by norm_num [Real.volume_Icc]
  rw [hu.integral_eq, hv, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), integral_id]
  norm_num

theorem uniform_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc 0 2) μ) :
    Integrable X μ :=
  (memLp_of_bounded (uniform_support μ X hu) hu.aemeasurable.aestronglyMeasurable 2).integrable
    (by norm_num)

theorem centered_uniform_subgaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc 0 2) μ) :
    (∫ omega, X omega - 1 ∂μ) = 0 ∧
      (∀ᵐ omega ∂μ, X omega - 1 ∈ Icc (-1 : ℝ) 1) ∧
      HasSubgaussianMGF (fun omega => X omega - 1) 1 μ := by
  have hi := uniform_integrable μ X hu
  have hm : (∫ omega, X omega - 1 ∂μ) = 0 := by
    rw [integral_sub hi (integrable_const 1), uniform_mean_one μ X hu]
    simp
  have hb : ∀ᵐ omega ∂μ, X omega - 1 ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [uniform_support μ X hu] with omega hb
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨hm, hb, ?_⟩
  have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (hu.aemeasurable.sub_const 1) hb hm
  have hp : (‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 = (1 : ℝ≥0) := by
    norm_num [← NNReal.coe_inj]
  rw [hp] at hh
  exact hh

theorem uniform_sample_mean_converges_to_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hu : ∀ i, pdf.IsUniform (X i) (Icc 0 2) μ)
    (hind : Pairwise ((· ⟂ᵢ[μ] ·) on X)) :
    ∀ᵐ omega ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i omega) / (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  simpa only [uniform_mean_one μ (X 0) (hu 0)] using
    strong_law_ae_real X (uniform_integrable μ (X 0) (hu 0)) hind
      (fun i => (hu i).identDistrib (hu 0))

theorem uniform_sample_mean_does_not_converge_to_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hu : ∀ i, pdf.IsUniform (X i) (Icc 0 2) μ)
    (hind : Pairwise ((· ⟂ᵢ[μ] ·) on X)) :
    ∀ᵐ omega ∂μ, ¬ Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i omega) / (n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [uniform_sample_mean_converges_to_one μ X hu hind] with omega homega
  intro hz
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique homega hz
  norm_num at he

theorem removed_bias_is_still_in_the_observation {Ω : Type*} (X : Ω → ℝ) (omega : Ω) :
    X omega = 1 + (X omega - 1) := by ring

theorem actual_uniform_mgf_quadratic_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hu : pdf.IsUniform X (Icc 0 2) μ) (lambda : ℝ) (hl : |lambda| ≤ 1 / 2) :
    |mgf X μ lambda - 1 - lambda| ≤ 4 * lambda ^ 2 := by
  have hi := uniform_integrable μ X hu
  have he : Integrable (fun omega => Real.exp (lambda * X omega)) μ :=
    integrable_exp_mul_of_mem_Icc hu.aemeasurable (uniform_support μ X hu)
  have hpoint : ∀ᵐ omega ∂μ,
      ‖Real.exp (lambda * X omega) - 1 - lambda * X omega‖ ≤ 4 * lambda ^ 2 := by
    filter_upwards [uniform_support μ X hu] with omega hb
    have hn : ‖lambda * X omega‖ ≤ 1 := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb.1]
      calc
        |lambda| * X omega ≤ (1 / 2 : ℝ) * 2 := mul_le_mul hl hb.2 hb.1 (by norm_num)
        _ = 1 := by norm_num
    have hh := Real.norm_exp_sub_one_sub_id_le hn
    have hs : ‖lambda * X omega‖ ^ 2 ≤ 4 * lambda ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      have hx : (X omega) ^ 2 ≤ 4 := by nlinarith [hb.1, hb.2]
      have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg lambda)
      nlinarith only [hh]
    exact hh.trans hs
  have hbound := norm_integral_le_of_norm_le_const hpoint
  have hid : (∫ omega, Real.exp (lambda * X omega) - 1 - lambda * X omega ∂μ) =
      mgf X μ lambda - 1 - lambda := by
    have hs : Integrable (fun omega => Real.exp (lambda * X omega) - 1) μ := by
      simpa only [Pi.sub_def] using he.sub (integrable_const 1)
    rw [integral_sub hs (hi.const_mul lambda),
      integral_sub he (integrable_const 1), integral_const_mul,
      uniform_mean_one μ X hu]
    simp [mgf]
  rw [hid] at hbound
  simpa [Real.norm_eq_abs] using hbound

theorem positive_uniform_mgf_violates_parameter_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hu : pdf.IsUniform X (Icc 0 2) μ) (lambda : ℝ)
    (hl : 0 < lambda) (hsmall : lambda ≤ 1 / 4) :
    Real.exp (lambda ^ 2 * 2 ^ 2 / 2) < mgf X μ lambda := by
  have hi := uniform_integrable μ X hu
  have he : Integrable (fun omega => Real.exp (lambda * X omega)) μ :=
    integrable_exp_mul_of_mem_Icc hu.aemeasurable (uniform_support μ X hu)
  have hlo : 1 + lambda ≤ mgf X μ lambda := by
    have hlin : Integrable (fun omega => 1 + lambda * X omega) μ := by
      simpa only [Pi.add_def] using (integrable_const 1 |>.add (hi.const_mul lambda))
    have hh := integral_mono hlin he
      (fun omega => by simpa [add_comm] using Real.add_one_le_exp (lambda * X omega))
    rw [integral_add (integrable_const 1) (hi.const_mul lambda), integral_const_mul,
      uniform_mean_one μ X hu] at hh
    simpa [mgf, add_comm] using hh
  have hnorm : ‖lambda ^ 2 * 2 ^ 2 / 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hh := Real.norm_exp_sub_one_sub_id_le hnorm
  rw [Real.norm_eq_abs] at hh
  have hexp := (abs_le.mp hh).2
  have hsq : ‖lambda ^ 2 * 2 ^ 2 / 2‖ ^ 2 = 4 * lambda ^ 4 := by
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [hsq] at hexp
  have hpower : lambda ^ 4 ≤ lambda ^ 2 / 16 := by
    have hs : lambda ^ 2 ≤ 1 / 16 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg lambda)
    nlinarith only [hp]
  have hexp_small : Real.exp (lambda ^ 2 * 2 ^ 2 / 2) < 1 + lambda := by
    nlinarith
  exact hexp_small.trans_le hlo

theorem uniform_not_subgaussian_parameter_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hu : pdf.IsUniform X (Icc 0 2) μ) : ¬ HasSubgaussianMGF X 4 μ := by
  intro h
  have hh := positive_uniform_mgf_violates_parameter_two μ X hu (1 / 4)
    (by norm_num) (by norm_num)
  have hm := h.mgf_le (1 / 4)
  norm_num only [NNReal.coe_ofNat] at hm
  nlinarith

end SafeLearning.CompleteAppliedUniformBias
