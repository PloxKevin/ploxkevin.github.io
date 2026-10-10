import SafeLearning.CompleteAppliedUniformLawMGF
import SafeLearning.CompleteAppliedUniformOptimalSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedUniformLawOptimal
open SafeLearning.CompleteAppliedUniformLawMGF
open SafeLearning.CompleteAppliedUniformMGFSeries
open SafeLearning.CompleteAppliedUniformOptimalSeries

theorem actual_uniform_variance_is_the_variance_proxy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) :
    variance X μ=a^2/3 := by
  have hav : volume (Icc (-a) a)=ENNReal.ofReal (2*a) := by
    rw [Real.volume_Icc];congr 1;ring
  have hcomp : (∫ omega,(X omega)^2 ∂μ)=
      (volume (Icc (-a) a))⁻¹.toReal*(∫ x in Icc (-a) a,x^2) := by
    have h := integral_map hu.aemeasurable
      ((continuous_id.pow 2 : Continuous (fun x : ℝ=>x^2)).aestronglyMeasurable)
    rw [hu.map_eq] at h
    simpa only [ProbabilityTheory.cond,integral_smul_measure,smul_eq_mul,Function.comp_apply,Pi.pow_apply,id_eq] using h.symm
  rw [variance_of_integral_eq_zero hu.aemeasurable
    (actual_symmetric_uniform_expectation_is_zero μ X a ha hu),hcomp,hav,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (by positivity),
    integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : -a≤a),integral_pow]
  have ha0 : a≠0 := ha.ne'
  field_simp
  ring

theorem actual_uniform_subgaussian_variance_proxies_are_exactly_those_above_the_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) (c : ℝ≥0) :
    HasSubgaussianMGF X c μ ↔ a^2/3≤(c:ℝ) := by
  constructor
  · intro h
    by_contra hno
    have ha2 : 0<a^2 := sq_pos_of_pos ha
    have hcsmall : (c:ℝ)/a^2<1/3 := by
      apply (div_lt_iff₀ ha2).mpr
      have hc : (c:ℝ)<a^2/3 := lt_of_not_ge hno
      linarith
    obtain ⟨t,ht,hviolate⟩ :=
      actual_every_smaller_uniform_variance_proxy_has_a_true_mgf_violation
        ((c:ℝ)/a^2) (div_nonneg c.coe_nonneg ha2.le) hcsmall
    have hbound := h.mgf_le (t/a)
    rw [actual_uniform_law_mgf_is_the_normalized_hyperbolic_sine μ X a ha hu] at hbound
    have ha0 : a≠0 := ha.ne'
    rw [show a*(t/a)=t by field_simp] at hbound
    have hexp : (c:ℝ)*(t/a)^2/2=((c:ℝ)/a^2)*t^2/2 := by field_simp
    rw [hexp] at hbound
    linarith
  · intro hc
    have hbase := actual_uniform_law_has_the_true_variance_proxy_subgaussian_mgf μ X a ha hu
    refine ⟨hbase.integrable_exp_mul,fun t=>(hbase.mgf_le t).trans ?_⟩
    apply Real.exp_le_exp.mpr
    change (a^2/3)*t^2/2≤(c:ℝ)*t^2/2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) (by norm_num)

theorem actual_uniform_variance_is_the_attained_least_subgaussian_variance_proxy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) :
    IsLeast {c : ℝ≥0|HasSubgaussianMGF X c μ} ⟨a^2/3,by positivity⟩ := by
  refine ⟨actual_uniform_law_has_the_true_variance_proxy_subgaussian_mgf μ X a ha hu,?_⟩
  intro c hc
  exact_mod_cast (actual_uniform_subgaussian_variance_proxies_are_exactly_those_above_the_variance
    μ X a ha hu c).mp hc

theorem actual_uniform_standard_deviation_is_the_attained_least_radius_parameter
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a : ℝ) (ha : 0<a) (hu : pdf.IsUniform X (Icc (-a) a) μ) :
    IsLeast {r : ℝ|0≤r ∧ HasSubgaussianMGF X ⟨r^2,by positivity⟩ μ} (a/Real.sqrt 3) := by
  have hs : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hsq : (a/Real.sqrt 3)^2=a^2/3 := by rw [div_pow,hs2]
  have hp : 0≤a/Real.sqrt 3 := div_nonneg ha.le hs.le
  refine ⟨⟨hp,?_⟩,?_⟩
  · apply (actual_uniform_subgaussian_variance_proxies_are_exactly_those_above_the_variance
      μ X a ha hu _).mpr
    change a^2/3≤(a/Real.sqrt 3)^2
    rw [hsq]
  · intro r hr
    have hc := (actual_uniform_subgaussian_variance_proxies_are_exactly_those_above_the_variance
      μ X a ha hu ⟨r^2,by positivity⟩).mp hr.2
    change a^2/3≤r^2 at hc
    nlinarith [hsq,hr.1,hp]

end SafeLearning.CompleteAppliedUniformLawOptimal
