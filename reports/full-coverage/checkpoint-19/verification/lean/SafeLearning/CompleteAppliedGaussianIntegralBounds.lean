import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SafeLearning.CompleteAppliedGaussianIntegralBounds

def eighthPolynomial (x : ℝ) : ℝ :=
  ∑i∈Finset.range 8,(-x^2/2)^i/(i.factorial:ℝ)

theorem actual_uniform_exponential_polynomial_error_on_unit_interval
    (x : ℝ) (hx : x∈Icc (0:ℝ) 1) :
    |Real.exp (-x^2/2)-eighthPolynomial x|≤1/9000000 := by
  have hx2 : 0≤x^2 ∧ x^2≤1 := ⟨sq_nonneg _,by nlinarith [hx.1,hx.2]⟩
  have he : |(-x^2/2)|≤(1/2:ℝ) := by
    rw [abs_of_nonpos (by nlinarith : -x^2/2≤0)]
    nlinarith
  have hp := pow_le_pow_left₀ (abs_nonneg (-x^2/2)) he 8
  have hb := Real.exp_bound (x:=(-x^2/2)) (by linarith : |(-x^2/2)|≤1)
    (n:=8) (by norm_num)
  change |Real.exp (-x^2/2)-eighthPolynomial x|≤_ at hb
  norm_num at hp hb
  nlinarith

theorem actual_polynomial_unit_interval_integral :
    (∫x in (0:ℝ)..1,eighthPolynomial x)=
    1-1/6+1/40-1/336+1/3456-1/42240+1/599040-1/9676800 := by
  have hterm (i : ℕ) :
      (∫x in (0:ℝ)..1,(-x^2/2)^i/(i.factorial:ℝ))=
      (-1/2:ℝ)^i/((i.factorial:ℝ)*(2*i+1)) := by
    have he : (fun x : ℝ=>(-x^2/2)^i/(i.factorial:ℝ))=
        (fun x : ℝ=>((-1/2:ℝ)^i/(i.factorial:ℝ))*x^(2*i)) := by
      funext x
      have h : -x^2/2=(-1/2:ℝ)*x^2 := by ring
      rw [h,mul_pow,←pow_mul]
      ring
    rw [he,intervalIntegral.integral_const_mul,integral_pow]
    simp
    field_simp
  unfold eighthPolynomial
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hterm]
    norm_num [Finset.sum_range_succ,Nat.factorial]
  · intro i hi
    exact (by fun_prop : Continuous (fun x : ℝ=>(-x^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _

theorem actual_standard_gaussian_exponential_integral_error_bound :
    |(∫x in (0:ℝ)..1,Real.exp (-x^2/2))-
      (1-1/6+1/40-1/336+1/3456-1/42240+1/599040-1/9676800)|≤1/9000000 := by
  have he : |∫x in (0:ℝ)..1,(Real.exp (-x^2/2)-eighthPolynomial x)|≤1/9000000 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
      (C:=1/9000000) (f:=fun x=>Real.exp (-x^2/2)-eighthPolynomial x) (by
        intro x hx
        rw [Real.norm_eq_abs]
        exact actual_uniform_exponential_polynomial_error_on_unit_interval x
          ⟨(by simpa using hx.1.le),(by simpa using hx.2)⟩)
    simpa using h
  rw [intervalIntegral.integral_sub] at he
  · rw [actual_polynomial_unit_interval_integral] at he
    exact he
  · exact (by fun_prop : Continuous (fun x : ℝ=>Real.exp (-x^2/2))).intervalIntegrable _ _
  · unfold eighthPolynomial
    exact (by fun_prop : Continuous (fun x : ℝ=>∑i∈Finset.range 8,(-x^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _

theorem actual_gaussian_exponential_integral_rational_enclosure :
    (85562427/100000000:ℝ)<(∫x in (0:ℝ)..1,Real.exp (-x^2/2)) ∧
    (∫x in (0:ℝ)..1,Real.exp (-x^2/2))<(85562450/100000000:ℝ) := by
  have hb := abs_le.mp actual_standard_gaussian_exponential_integral_error_bound
  constructor <;> linarith

end SafeLearning.CompleteAppliedGaussianIntegralBounds
