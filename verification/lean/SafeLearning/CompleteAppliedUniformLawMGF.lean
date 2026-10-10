import SafeLearning.CompleteAppliedUniformMGFSeries
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedUniformLawMGF
open SafeLearning.CompleteAppliedUniformMGFSeries

theorem actual_symmetric_uniform_law_has_its_literal_support
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ)
    (hu : pdf.IsUniform X (Icc (-a) a) μ) :
    ∀ᵐ omega ∂μ,X omega∈Icc (-a) a := by
  apply (hu.ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem actual_symmetric_uniform_expectation_is_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ) (ha : 0<a)
    (hu : pdf.IsUniform X (Icc (-a) a) μ) : (∫ omega,X omega ∂μ)=0 := by
  rw [hu.integral_eq,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : -a≤a),integral_id]
  ring

theorem actual_uniform_law_mgf_is_the_normalized_hyperbolic_sine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) (t : ℝ) :
    mgf X μ t=normalizedSinh (a*t) := by
  by_cases ht : t=0
  · simp [mgf,ht,normalizedSinh]
  have ha0 : a≠0 := ha.ne'
  have hav : volume (Icc (-a) a)=ENNReal.ofReal (2*a) := by
    rw [Real.volume_Icc];congr 1;ring
  have hcomp : (∫ omega,Real.exp (t*X omega) ∂μ)=
      (volume (Icc (-a) a))⁻¹.toReal*(∫ x in Icc (-a) a,Real.exp (t*x)) := by
    have hc : Continuous (fun x : ℝ=>Real.exp (t*x)) := by fun_prop
    have h := integral_map hu.aemeasurable hc.aestronglyMeasurable
    rw [hu.map_eq] at h
    simpa only [ProbabilityTheory.cond,integral_smul_measure,smul_eq_mul,Function.comp_apply] using h.symm
  rw [mgf,hcomp,hav,ENNReal.toReal_inv,ENNReal.toReal_ofReal (by positivity),
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : -a≤a)]
  have hint := intervalIntegral.mul_integral_comp_mul_left (f:=Real.exp) (a:=-a) (b:=a) t
  rw [integral_exp] at hint
  have hat : a*t≠0 := mul_ne_zero ha0 ht
  rw [normalizedSinh,ite_eq_right hat,Real.sinh_eq]
  have he : t*(-a)=-(a*t) := by ring
  rw [he,mul_comm t a] at hint
  field_simp
  nlinarith [hint]

theorem actual_uniform_law_has_the_true_variance_proxy_subgaussian_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) :
    HasSubgaussianMGF X ⟨a^2/3,by positivity⟩ μ := by
  refine ⟨fun t=>integrable_exp_mul_of_mem_Icc hu.aemeasurable
    (actual_symmetric_uniform_law_has_its_literal_support μ X a hu),fun t=>?_⟩
  rw [actual_uniform_law_mgf_is_the_normalized_hyperbolic_sine μ X a ha hu t]
  have h := actual_uniform_moment_series_is_bounded_by_the_variance_proxy_exponential (a*t)
  calc
    _≤Real.exp ((a*t)^2/6) := h
    _=_ := by congr 1;change (a*t)^2/6=(a^2/3)*t^2/2;ring

end SafeLearning.CompleteAppliedUniformLawMGF
