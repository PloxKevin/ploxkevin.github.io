import SafeLearning.CompleteAppliedGaussianGeneralIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteAppliedGaussianTailIntegral
open CompleteAppliedGaussianGeneralIntegral

def fiftiethPolynomial (value : ℝ) : ℝ :=
  ∑i∈Finset.range 50,(-value^2/2)^i/(i.factorial:ℝ)
def actualTailPolynomialIntegral (radius : ℝ) : ℝ :=
  ∑i∈Finset.range 50,(-1/2:ℝ)^i*radius^(2*i+1)/((i.factorial:ℝ)*(2*i+1))

theorem actual_uniform_fiftieth_order_gaussian_exponential_error_through_radius_four
    (value : ℝ) (hvalue : value∈Icc (0:ℝ) 4) :
    |Real.exp (-value^2/2)-fiftiethPolynomial value|≤1/10000000000000000 := by
  have hs : value^2≤16 := by nlinarith [hvalue.1,hvalue.2]
  have ha : |(-value^2/2)|≤(8:ℝ) := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg value] : -value^2/2≤0)]
    nlinarith
  have hb := actual_real_exponential_series_error_with_the_general_tail_ratio
    (-value^2/2) 50 (by norm_num;linarith)
  have hp := pow_le_pow_left₀ (abs_nonneg (-value^2/2)) ha 50
  change |Real.exp (-value^2/2)-fiftiethPolynomial value|≤_ at hb
  norm_num [Nat.factorial] at hb hp
  nlinarith

theorem actual_fiftieth_gaussian_polynomial_integral_at_every_radius (radius : ℝ) :
    (∫value in (0:ℝ)..radius,fiftiethPolynomial value)=actualTailPolynomialIntegral radius := by
  have hterm (i : ℕ) :
      (∫value in (0:ℝ)..radius,(-value^2/2)^i/(i.factorial:ℝ))=
        (-1/2:ℝ)^i*radius^(2*i+1)/((i.factorial:ℝ)*(2*i+1)) := by
    have he : (fun value : ℝ=>(-value^2/2)^i/(i.factorial:ℝ))=
        (fun value=>((-1/2:ℝ)^i/(i.factorial:ℝ))*value^(2*i)) := by
      funext value
      have hz : -value^2/2=(-1/2:ℝ)*value^2 := by ring
      rw [hz,mul_pow,←pow_mul];ring
    rw [he,intervalIntegral.integral_const_mul,integral_pow]
    simp
    field_simp
  unfold fiftiethPolynomial actualTailPolynomialIntegral
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi;exact hterm i
  · intro i hi
    exact (by fun_prop : Continuous (fun value : ℝ=>(-value^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _

theorem actual_gaussian_exponential_tail_integral_uniform_rational_error
    (radius : ℝ) (hradius : radius∈Icc (0:ℝ) 4) :
    |(∫value in (0:ℝ)..radius,Real.exp (-value^2/2))-actualTailPolynomialIntegral radius|≤
      1/2500000000000000 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=radius) (C:=1/10000000000000000)
    (f:=fun value=>Real.exp (-value^2/2)-fiftiethPolynomial value) (by
      intro value hvalue
      rw [Real.norm_eq_abs]
      apply actual_uniform_fiftieth_order_gaussian_exponential_error_through_radius_four
      rw [uIoc_of_le hradius.1] at hvalue
      exact ⟨hvalue.1.le,hvalue.2.trans hradius.2⟩)
  have he : |(∫value in (0:ℝ)..radius,Real.exp (-value^2/2))-actualTailPolynomialIntegral radius|≤
      radius/10000000000000000 := by
    rw [intervalIntegral.integral_sub,actual_fiftieth_gaussian_polynomial_integral_at_every_radius,
      Real.norm_eq_abs,sub_zero,abs_of_nonneg hradius.1] at hb
    · simpa only [div_eq_mul_inv,mul_comm,one_mul] using hb
    · exact (by fun_prop : Continuous (fun value : ℝ=>Real.exp (-value^2/2))).intervalIntegrable _ _
    · unfold fiftiethPolynomial
      exact (by fun_prop : Continuous (fun value : ℝ=>∑i∈Finset.range 50,(-value^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _
  linarith [hradius.2]

end SafeLearning.CompleteAppliedGaussianTailIntegral
