import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedCoverageBeta

def coverageLaw : Measure ℝ := betaMeasure 18 2
instance coverageLaw_probability : IsProbabilityMeasure coverageLaw :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

theorem actual_beta_eighteen_two_normalizer_is_the_true_rational :
    beta (18:ℝ) 2=1/342 := by
  have h18:=Real.Gamma_nat_eq_factorial 17
  have h2:=Real.Gamma_nat_eq_factorial 1
  have h20:=Real.Gamma_nat_eq_factorial 19
  norm_num [Nat.factorial] at h18 h2 h20
  norm_num [beta,h18,h2,h20]

theorem actual_beta_eighteen_two_density_is_the_literal_polynomial (x : ℝ) :
    betaPDFReal 18 2 x=(Ioo (0:ℝ) 1).indicator (fun u=>342*u^17*(1-u)) x := by
  rw [betaPDFReal]
  by_cases hx : 0<x ∧ x<1
  · rw [if_pos hx,indicator_of_mem (show x∈Ioo (0:ℝ) 1 from hx)]
    rw [actual_beta_eighteen_two_normalizer_is_the_true_rational]
    norm_num [Real.rpow_natCast]
  · simp [hx]

theorem actual_beta_eighteen_two_density_is_nonnegative (x : ℝ) :
    0≤betaPDFReal 18 2 x := by
  rw [actual_beta_eighteen_two_density_is_the_literal_polynomial]
  by_cases hx : x∈Ioo (0:ℝ) 1
  · rw [indicator_of_mem hx]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx.1.le _)) (by linarith [hx.2])
  · rw [indicator_of_notMem hx]

theorem actual_beta_polynomial_expectation_integral (g : ℝ→ℝ) :
    (∫x,g x ∂coverageLaw)=∫x in (0:ℝ)..1,342*x^17*(1-x)*g x := by
  unfold coverageLaw betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (by exact (measurable_betaPDFReal 18 2).ennreal_ofReal)
    (by exact Filter.Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]
  simp only [betaPDF]
  simp only [ENNReal.toReal_ofReal (actual_beta_eighteen_two_density_is_nonnegative _),smul_eq_mul]
  simp only [actual_beta_eighteen_two_density_is_the_literal_polynomial]
  have he : (fun x=>(Ioo (0:ℝ) 1).indicator (fun u=>342*u^17*(1-u)) x*g x)=
      (Ioo (0:ℝ) 1).indicator (fun x=>342*x^17*(1-x)*g x) := by
    funext x
    by_cases hx : x∈Ioo (0:ℝ) 1
    · simp [hx]
    · simp [hx]
  rw [he,integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

theorem actual_beta_all_natural_moments_are_integrable (n : ℕ) :
    Integrable (fun x:ℝ=>x^n) coverageLaw := by
  unfold coverageLaw betaMeasure
  rw [integrable_withDensity_iff
    (show Measurable (betaPDF 18 2) from (measurable_betaPDFReal 18 2).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]
  simp only [betaPDF]
  simp only [ENNReal.toReal_ofReal (actual_beta_eighteen_two_density_is_nonnegative _)]
  simp only [actual_beta_eighteen_two_density_is_the_literal_polynomial]
  have he : (fun x=>x^n*(Ioo (0:ℝ) 1).indicator (fun u=>342*u^17*(1-u)) x)=
      (Ioo (0:ℝ) 1).indicator (fun x=>x^n*(342*x^17*(1-x))) := by
    funext x
    by_cases hx : x∈Ioo (0:ℝ) 1 <;>simp [hx]
  rw [he,integrable_indicator_iff measurableSet_Ioo]
  exact ((show Continuous (fun x:ℝ=>x^n*(342*x^17*(1-x))) by fun_prop).integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem actual_beta_natural_moment_has_its_true_integral_value (n : ℕ) :
    (∫x:ℝ,x^n ∂coverageLaw)=342*((1:ℝ)/(n+18)-1/(n+19)) := by
  rw [actual_beta_polynomial_expectation_integral]
  have he : (fun x:ℝ=>342*x^17*(1-x)*x^n)=
      (fun x:ℝ=>342*(x^(n+17)-x^(n+18))) := by
    funext x
    simp only [pow_add]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (by exact (continuous_id.pow _).intervalIntegrable _ _) (by exact (continuous_id.pow _).intervalIntegrable _ _),integral_pow,integral_pow]
  norm_num
  congr 1 <;> norm_num [Nat.cast_add] <;> ring

theorem actual_beta_coverage_mean_variance_and_test_noise_moment :
    (∫x:ℝ,x ∂coverageLaw)=9/10 ∧
      Var[fun x:ℝ=>x;coverageLaw]=3/700 ∧
      (∫x:ℝ,x*(1-x) ∂coverageLaw)=3/35 := by
  have h1:=actual_beta_natural_moment_has_its_true_integral_value 1
  have h2:=actual_beta_natural_moment_has_its_true_integral_value 2
  norm_num at h1 h2
  have hi : Integrable (fun x:ℝ=>x) coverageLaw := by
    simpa using actual_beta_all_natural_moments_are_integrable 1
  have hs:=actual_beta_all_natural_moments_are_integrable 2
  have hl : MemLp (fun x:ℝ=>x) 2 coverageLaw :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hs
  refine ⟨h1,?_,?_⟩
  · rw [variance_eq_sub hl,h1]
    change (∫x:ℝ,x^2 ∂coverageLaw)-(9/10)^2=3/700
    rw [h2]
    norm_num
  · have he : (fun x:ℝ=>x*(1-x))=(fun x:ℝ=>x-x^2) := by funext x;ring
    rw [he,integral_sub hi hs,h1,h2]
    norm_num

end SafeLearning.CompleteAppliedCoverageBeta
