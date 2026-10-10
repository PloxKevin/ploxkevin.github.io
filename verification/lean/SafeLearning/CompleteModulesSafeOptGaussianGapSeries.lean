import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesSafeOptGaussianGapSeries

def actualGaussianFeature (n : ℕ) (x : ℝ) : ℝ :=
  x^n*Real.exp (-(x^2)/2)/Real.sqrt (n.factorial:ℝ)
def actualGaussianKernel (x y : ℝ) : ℝ := Real.exp (-((x-y)^2)/2)
def actualGapFunction (x : ℝ) : ℝ := (x-1/20)*(x-3/20)*Real.exp (-(x^2)/2)

theorem actual_gaussian_feature_products_are_the_true_scaled_exponential_series
    (n : ℕ) (x y : ℝ) :
    actualGaussianFeature n x*actualGaussianFeature n y=
      Real.exp (-(x^2)/2)*Real.exp (-(y^2)/2)*((x*y)^n/(n.factorial:ℝ)) := by
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hs : (Real.sqrt (n.factorial:ℝ))^2=(n.factorial:ℝ) := Real.sq_sqrt hf.le
  have hn : Real.sqrt (n.factorial:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.2 hf)
  unfold actualGaussianFeature
  rw [mul_pow]
  field_simp
  rw [hs]
  ring

theorem actual_squared_exponential_kernel_has_the_literal_infinite_feature_expansion
    (x y : ℝ) : HasSum (fun n => actualGaussianFeature n x*actualGaussianFeature n y)
      (actualGaussianKernel x y) := by
  have he : HasSum (fun n : ℕ => (x*y)^n/(n.factorial:ℝ)) (Real.exp (x*y)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (x*y)
  have h := he.mul_left (Real.exp (-(x^2)/2)*Real.exp (-(y^2)/2))
  convert h using 1
  · funext n
    exact actual_gaussian_feature_products_are_the_true_scaled_exponential_series n x y
  · unfold actualGaussianKernel
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring

theorem actual_gaussian_feature_vector_has_unit_sum_of_squares (x : ℝ) :
    HasSum (fun n => (actualGaussianFeature n x)^2) 1 := by
  simpa [pow_two,actualGaussianKernel] using
    actual_squared_exponential_kernel_has_the_literal_infinite_feature_expansion x x

theorem actual_source_gap_function_is_exactly_the_printed_three_feature_combination (x : ℝ) :
    actualGapFunction x=Real.sqrt 2*actualGaussianFeature 2 x-
      (1/5:ℝ)*actualGaussianFeature 1 x+(3/400:ℝ)*actualGaussianFeature 0 x := by
  have hsqrt : Real.sqrt (2:ℝ)≠0 := by positivity
  unfold actualGapFunction actualGaussianFeature
  norm_num [Nat.factorial]
  field_simp
  ring

theorem actual_source_coefficient_squared_norm_and_nearest_three_decimal_norm_are_exact :
    (Real.sqrt (2:ℝ))^2+(-(1/5:ℝ))^2+(3/400:ℝ)^2=326409/160000 ∧
      |Real.sqrt (326409/160000:ℝ)-357/250|<1/2000 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤326409/160000)
  have hn := Real.sqrt_nonneg (326409/160000:ℝ)
  constructor
  · norm_num [hs2]
  · rw [abs_lt]
    constructor <;> nlinarith

theorem actual_source_middle_gap_is_unsafe_and_rounds_to_negative_point_zero_zero_two_five :
    actualGapFunction (1/10)<0 ∧
      |actualGapFunction (1/10)-(-(1/400:ℝ))|<1/20000 := by
  have hepos := Real.exp_pos (-(1/200:ℝ))
  have helo : (199/200:ℝ)≤Real.exp (-(1/200:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/200:ℝ))]
  have hehi : Real.exp (-(1/200:ℝ))≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hf : actualGapFunction (1/10)=-(1/400:ℝ)*Real.exp (-(1/200:ℝ)) := by
    norm_num [actualGapFunction]
  rw [hf]
  refine ⟨by nlinarith,?_⟩
  rw [abs_lt]
  constructor <;> nlinarith

end SafeLearning.CompleteModulesSafeOptGaussianGapSeries
