import SafeLearning.CompleteAppliedGaussianCDF

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteAppliedGaussianGeneralIntegral
open CompleteAppliedGaussianCDF

theorem actual_real_exponential_series_error_with_the_general_tail_ratio
    (value : ℝ) (degree : ℕ) (hratio : |value|/(degree+1:ℝ)≤1/2) :
    |Real.exp value-(∑i∈Finset.range degree,value^i/(i.factorial:ℝ))|≤
      |value|^degree/(degree.factorial:ℝ)*2 := by
  have hc : ‖(value:ℂ)‖/(degree.succ:ℝ)≤1/2 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,Nat.cast_succ] using hratio
  convert Complex.exp_bound' hc using 1 <;> norm_cast

def twentiethPolynomial (value : ℝ) : ℝ :=
  ∑i∈Finset.range 20,(-value^2/2)^i/(i.factorial:ℝ)

def actualPolynomialIntegral (radius : ℝ) : ℝ :=
  ∑i∈Finset.range 20,(-1/2:ℝ)^i*radius^(2*i+1)/((i.factorial:ℝ)*(2*i+1))

theorem actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
    (value : ℝ) (hvalue : value∈Icc (0:ℝ) 2) :
    |Real.exp (-value^2/2)-twentiethPolynomial value|≤1/1000000000000 := by
  have hs : value^2≤4 := by nlinarith [hvalue.1,hvalue.2]
  have ha : |(-value^2/2)|≤(2:ℝ) := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg value] : -value^2/2≤0)]
    nlinarith
  have hb := actual_real_exponential_series_error_with_the_general_tail_ratio
    (-value^2/2) 20 (by norm_num;linarith)
  have hp := pow_le_pow_left₀ (abs_nonneg (-value^2/2)) ha 20
  change |Real.exp (-value^2/2)-twentiethPolynomial value|≤_ at hb
  norm_num [Nat.factorial] at hb hp
  nlinarith

theorem actual_gaussian_polynomial_integral_at_every_radius (radius : ℝ) :
    (∫value in (0:ℝ)..radius,twentiethPolynomial value)=actualPolynomialIntegral radius := by
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
  unfold twentiethPolynomial actualPolynomialIntegral
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi;exact hterm i
  · intro i hi
    exact (by fun_prop : Continuous (fun value : ℝ=>(-value^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _

theorem actual_gaussian_exponential_integral_uniform_rational_error
    (radius : ℝ) (hradius : radius∈Icc (0:ℝ) 2) :
    |(∫value in (0:ℝ)..radius,Real.exp (-value^2/2))-actualPolynomialIntegral radius|≤
      1/500000000000 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=radius) (C:=1/1000000000000)
    (f:=fun value=>Real.exp (-value^2/2)-twentiethPolynomial value) (by
      intro value hvalue
      rw [Real.norm_eq_abs]
      apply actual_uniform_twentieth_order_gaussian_exponential_error_through_radius_two
      rw [uIoc_of_le hradius.1] at hvalue
      exact ⟨hvalue.1.le,hvalue.2.trans hradius.2⟩)
  have he : |(∫value in (0:ℝ)..radius,Real.exp (-value^2/2))-actualPolynomialIntegral radius|≤
      radius/1000000000000 := by
    rw [intervalIntegral.integral_sub,
      actual_gaussian_polynomial_integral_at_every_radius,Real.norm_eq_abs,
      sub_zero,abs_of_nonneg hradius.1] at hb
    · simpa only [div_eq_mul_inv,mul_comm,one_mul] using hb
    · exact (by fun_prop : Continuous (fun value : ℝ=>Real.exp (-value^2/2))).intervalIntegrable _ _
    · unfold twentiethPolynomial
      exact (by fun_prop : Continuous (fun value : ℝ=>∑i∈Finset.range 20,(-value^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _
  linarith [hradius.2]

theorem actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral
    (radius : ℝ) :
    standardCDF radius=1/2+(Real.sqrt (2*Real.pi))⁻¹*
      (∫value in (0:ℝ)..radius,Real.exp (-value^2/2)) := by
  have hd := intervalIntegral.integral_Iic_sub_Iic
    ((integrable_gaussianPDFReal 0 1).integrableOn (s:=Iic (0:ℝ)))
    ((integrable_gaussianPDFReal 0 1).integrableOn (s:=Iic radius))
  rw [←actual_standard_gaussian_cdf_is_its_density_integral,
    ←actual_standard_gaussian_cdf_is_its_density_integral,
    actual_standard_gaussian_symmetry_and_half_mass] at hd
  have hf : gaussianPDFReal 0 1=
      (fun value : ℝ=>(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-value^2/2)) := by
    funext value;simp [gaussianPDFReal]
  rw [hf,intervalIntegral.integral_const_mul] at hd
  linarith

end SafeLearning.CompleteAppliedGaussianGeneralIntegral
