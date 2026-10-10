import SafeLearning.CompleteAppliedUniformLawOptimal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedUniformSourceNumbers
open SafeLearning.CompleteAppliedUniformLawMGF
open SafeLearning.CompleteAppliedUniformLawOptimal

theorem actual_source_uniform_standard_deviation_exact_forms_and_rounding :
    (2/5:ℝ)/Real.sqrt 12=(1/5:ℝ)/Real.sqrt 3 ∧
    ((1/5:ℝ)/Real.sqrt 3)^2=(1/75:ℝ) ∧
    |(1/5:ℝ)/Real.sqrt 3-(115/1000:ℝ)|≤1/2000 ∧
    (115/1000:ℝ)<(1/5:ℝ)/Real.sqrt 3 ∧
    (1/5:ℝ)/((1/5:ℝ)/Real.sqrt 3)=Real.sqrt 3 := by
  have hs : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs12 : 0≤Real.sqrt 12 := Real.sqrt_nonneg _
  have hs122 : (Real.sqrt 12)^2=12 := Real.sq_sqrt (by norm_num)
  have he : Real.sqrt 12=2*Real.sqrt 3 := by nlinarith
  have hsq : ((1/5:ℝ)/Real.sqrt 3)^2=(1/75:ℝ) := by rw [div_pow,hs2];norm_num
  have hp : 0<(1/5:ℝ)/Real.sqrt 3 := div_pos (by norm_num) hs
  refine ⟨?_,hsq,?_,?_,?_⟩
  · rw [he];ring
  · rw [abs_le];constructor <;> nlinarith [hsq]
  · nlinarith [hsq]
  · field_simp

theorem actual_source_symmetric_uniform_has_the_exact_variance_and_two_valid_parameters
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc (-(1/5):ℝ) (1/5)) μ) :
    (∫ omega,X omega ∂μ)=0 ∧ variance X μ=(1/75:ℝ) ∧
    HasSubgaussianMGF X (1/25) μ ∧ HasSubgaussianMGF X (1/75) μ := by
  have hm := actual_symmetric_uniform_expectation_is_zero μ X (1/5) (by norm_num) hu
  have hv := actual_uniform_variance_is_the_variance_proxy μ X (1/5) (by norm_num) hu
  have hh := actual_uniform_law_has_the_true_variance_proxy_subgaussian_mgf μ X (1/5) (by norm_num) hu
  norm_num at hv hh
  refine ⟨hm,hv,?_,hh⟩
  apply (actual_uniform_subgaussian_variance_proxies_are_exactly_those_above_the_variance
    μ X (1/5) (by norm_num) hu (1/25)).mpr
  norm_num

theorem actual_source_uniform_optimal_radius_is_the_standard_deviation_not_its_rounded_display
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hu : pdf.IsUniform X (Icc (-(1/5):ℝ) (1/5)) μ) :
    IsLeast {r : ℝ|0≤r ∧ HasSubgaussianMGF X ⟨r^2,by positivity⟩ μ}
      ((1/5:ℝ)/Real.sqrt 3) ∧
    ¬HasSubgaussianMGF X ⟨(115/1000:ℝ)^2,by positivity⟩ μ := by
  have hi := actual_uniform_standard_deviation_is_the_attained_least_radius_parameter
    μ X (1/5) (by norm_num) hu
  refine ⟨hi,?_⟩
  intro hbad
  have hr := hi.2 (show (115/1000:ℝ)∈{r : ℝ|0≤r ∧ HasSubgaussianMGF X ⟨r^2,by positivity⟩ μ}
    from ⟨by norm_num,hbad⟩)
  have hstrict := actual_source_uniform_standard_deviation_exact_forms_and_rounding.2.2.2.1
  linarith

end SafeLearning.CompleteAppliedUniformSourceNumbers
