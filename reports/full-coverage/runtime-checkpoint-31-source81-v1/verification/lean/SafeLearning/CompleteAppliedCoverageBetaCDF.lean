import SafeLearning.CompleteAppliedCoverageBeta

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedCoverageBetaCDF
open CompleteAppliedCoverageBeta

theorem actual_beta_strict_cdf_on_the_unit_interval (c : ℝ) (hc : c∈Icc (0:ℝ) 1) :
    coverageLaw.real (Iio c)=19*c^18-18*c^19 := by
  calc
    coverageLaw.real (Iio c)=(∫x:ℝ,(Iio c).indicator (fun _=>(1:ℝ)) x ∂coverageLaw) := by
      exact (integral_indicator_one (μ:=coverageLaw) (measurableSet_Iio (a:=c))).symm
    _=∫x in (0:ℝ)..1,342*x^17*(1-x)*(Iio c).indicator (fun _=>(1:ℝ)) x :=
      actual_beta_polynomial_expectation_integral _
    _=∫x in (0:ℝ)..c,342*(x^17-x^18) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      have he : (fun x:ℝ=>342*x^17*(1-x)*(Iio c).indicator (fun _=>(1:ℝ)) x)=
          (Iio c).indicator (fun x:ℝ=>342*(x^17-x^18)) := by
        funext x
        by_cases hx : x∈Iio c
        · simp only [indicator_of_mem hx]
          ring
        · simp [hx]
      rw [he,setIntegral_indicator measurableSet_Iio]
      have hset : Ioc (0:ℝ) 1∩Iio c=Ioo (0:ℝ) c := by
        ext x
        simp only [mem_inter_iff,mem_Ioc,mem_Iio,mem_Ioo]
        constructor
        · intro h;exact ⟨h.1.1,h.2⟩
        · intro h;exact ⟨⟨h.1,le_trans (le_of_lt h.2) hc.2⟩,h.2⟩
      rw [hset,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hc.1]
    _=19*c^18-18*c^19 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub ((show Continuous (fun x:ℝ=>x^17) by fun_prop).intervalIntegrable _ _)
          ((show Continuous (fun x:ℝ=>x^18) by fun_prop).intervalIntegrable _ _),integral_pow,integral_pow]
      norm_num
      ring

theorem actual_beta_low_coverage_probability_is_the_literal_binomial_polynomial :
    coverageLaw.real (Iio (4/5:ℝ))=19*(4/5:ℝ)^18*(1/5)+(4/5:ℝ)^19 := by
  rw [actual_beta_strict_cdf_on_the_unit_interval (4/5) (by constructor <;>norm_num)]
  ring

theorem actual_beta_low_coverage_probability_has_the_printed_rounding :
    |coverageLaw.real (Iio (4/5:ℝ))-(83/1000:ℝ)|<1/2000 ∧
      coverageLaw.real (Iio (4/5:ℝ))≠(83/1000:ℝ) := by
  rw [actual_beta_low_coverage_probability_is_the_literal_binomial_polynomial]
  norm_num

theorem actual_beta_variance_and_standard_deviation_have_the_source_roundings :
    |(3/700:ℝ)-(429/100000:ℝ)|<1/200000 ∧
      |Real.sqrt (3/700:ℝ)-(65/1000:ℝ)|<1/2000 ∧
      (3/700:ℝ)≠(429/100000:ℝ) := by
  have hs : Real.sqrt (3/700:ℝ)^2=3/700 := Real.sq_sqrt (by norm_num)
  have hn:=Real.sqrt_nonneg (3/700:ℝ)
  refine ⟨by norm_num,?_,by norm_num⟩
  rw [abs_lt]
  constructor <;>nlinarith

theorem actual_two_thousand_test_variance_expression_and_exact_one_percent_addition :
    (3/700:ℝ)+(3/35)/2000=303/70000 ∧
      ((3/35:ℝ)/2000)/(3/700)=1/100 ∧
      |(3/700:ℝ)-(4286/1000000:ℝ)|<1/2000000 ∧
      |(3/35:ℝ)-(857/10000:ℝ)|<1/20000 ∧
      |(303/70000:ℝ)-(4329/1000000:ℝ)|<1/2000000 ∧
      (3/700:ℝ)≠(4286/1000000:ℝ) ∧
      (3/35:ℝ)≠(857/10000:ℝ) ∧
      (303/70000:ℝ)≠(4329/1000000:ℝ) := by
  norm_num

theorem actual_measured_variance_square_root_has_the_source_rounding :
    |Real.sqrt (303/70000:ℝ)-(658/10000:ℝ)|<1/20000 := by
  have hs : Real.sqrt (303/70000:ℝ)^2=303/70000 := Real.sq_sqrt (by norm_num)
  have hn:=Real.sqrt_nonneg (303/70000:ℝ)
  rw [abs_lt]
  constructor <;>nlinarith

end SafeLearning.CompleteAppliedCoverageBetaCDF
