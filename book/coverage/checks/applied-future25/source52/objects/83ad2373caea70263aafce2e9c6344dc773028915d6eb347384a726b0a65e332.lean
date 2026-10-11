import SafeLearning.CompleteAppliedGaussianQuantile
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteAppliedGaussianMixtureCDFNumbers24
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianQuantile

def polynomial48 (x : ℝ) : ℝ := ∑ i∈Finset.range 48, (-x^2/2)^i/(i.factorial:ℝ)
def polynomialIntegral48 (r : ℝ) : ℝ :=
  ∑ i∈Finset.range 48,(-1/2:ℝ)^i*r^(2*i+1)/((i.factorial:ℝ)*(2*i+1))

theorem actual_degree48_exponential_error_through_radius_four
    (x : ℝ) (hx : x∈Icc (0:ℝ) 4) :
    |Real.exp (-x^2/2)-polynomial48 x| ≤ 1/1000000000000 := by
  have hs : x^2 ≤ 16 := by nlinarith [hx.1,hx.2]
  have ha : |(-x^2/2)| ≤ (8:ℝ) := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg x] : -x^2/2 ≤ 0)]; nlinarith
  have hb := actual_real_exponential_series_error_with_the_general_tail_ratio
    (-x^2/2) 48 (by norm_num; linarith)
  have hp := pow_le_pow_left₀ (abs_nonneg (-x^2/2)) ha 48
  change |Real.exp (-x^2/2)-polynomial48 x| ≤ _ at hb
  norm_num [Nat.factorial] at hb hp
  nlinarith

theorem actual_degree48_polynomial_integral (r : ℝ) :
    (∫ x in (0:ℝ)..r,polynomial48 x)=polynomialIntegral48 r := by
  have ht (i : ℕ) :
      (∫ x in (0:ℝ)..r,(-x^2/2)^i/(i.factorial:ℝ)) =
        (-1/2:ℝ)^i*r^(2*i+1)/((i.factorial:ℝ)*(2*i+1)) := by
    have he : (fun x : ℝ => (-x^2/2)^i/(i.factorial:ℝ)) =
        (fun x => ((-1/2:ℝ)^i/(i.factorial:ℝ))*x^(2*i)) := by
      funext x
      have hz : -x^2/2 = (-1/2:ℝ)*x^2 := by ring
      rw [hz,mul_pow,←pow_mul]; ring
    rw [he,intervalIntegral.integral_const_mul,integral_pow]
    simp; field_simp
  unfold polynomial48 polynomialIntegral48
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro i hi; exact ht i
  · intro i hi
    exact (by fun_prop : Continuous (fun x : ℝ => (-x^2/2)^i/(i.factorial:ℝ))).intervalIntegrable _ _

theorem actual_exponential_integral_error_through_radius_four
    (r : ℝ) (hr : r∈Icc (0:ℝ) 4) :
    |(∫ x in (0:ℝ)..r,Real.exp (-x^2/2))-polynomialIntegral48 r| ≤ 1/250000000000 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=r) (C:=1/1000000000000)
    (f:=fun x => Real.exp (-x^2/2)-polynomial48 x) (by
      intro x hx
      rw [Real.norm_eq_abs]
      apply actual_degree48_exponential_error_through_radius_four
      rw [uIoc_of_le hr.1] at hx
      exact ⟨hx.1.le,hx.2.trans hr.2⟩)
  have he : |(∫ x in (0:ℝ)..r,Real.exp (-x^2/2))-polynomialIntegral48 r| ≤ r/1000000000000 := by
    rw [intervalIntegral.integral_sub,actual_degree48_polynomial_integral,
      Real.norm_eq_abs,sub_zero,abs_of_nonneg hr.1] at hb
    · simpa only [div_eq_mul_inv,mul_comm,one_mul] using hb
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x^2/2))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous polynomial48).intervalIntegrable _ _
  linarith [hr.2]

theorem actual_CDF_two_certified :
    (97724986/100000000:ℝ) < standardCDF (2/1:ℝ) ∧
    standardCDF (2/1:ℝ) < 97724988/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_gaussian_exponential_integral_uniform_rational_error (2/1:ℝ) (by constructor <;> norm_num)
  have hp : (11962880133/10000000000:ℝ) < actualPolynomialIntegral (2/1:ℝ) ∧
      actualPolynomialIntegral (2/1:ℝ) < 11962880134/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_third_certified :
    (63055865/100000000:ℝ) < standardCDF (1/3:ℝ) ∧
    standardCDF (1/3:ℝ) < 63055867/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_gaussian_exponential_integral_uniform_rational_error (1/3:ℝ) (by constructor <;> norm_num)
  have hp : (3272620281/10000000000:ℝ) < actualPolynomialIntegral (1/3:ℝ) ∧
      actualPolynomialIntegral (1/3:ℝ) < 3272620282/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_five_thirds_certified :
    (95220964/100000000:ℝ) < standardCDF (5/3:ℝ) ∧
    standardCDF (5/3:ℝ) < 95220966/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_gaussian_exponential_integral_uniform_rational_error (5/3:ℝ) (by constructor <;> norm_num)
  have hp : (11335214890/10000000000:ℝ) < actualPolynomialIntegral (5/3:ℝ) ∧
      actualPolynomialIntegral (5/3:ℝ) < 11335214891/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_small_lower_certified :
    (76024782/100000000:ℝ) < standardCDF (7071/10000:ℝ) ∧
    standardCDF (7071/10000:ℝ) < 76024785/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_gaussian_exponential_integral_uniform_rational_error (7071/10000:ℝ) (by constructor <;> norm_num)
  have hp : (6523445741/10000000000:ℝ) < actualPolynomialIntegral (7071/10000:ℝ) ∧
      actualPolynomialIntegral (7071/10000:ℝ) < 6523445742/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_small_upper_certified :
    (76027889/100000000:ℝ) < standardCDF (442/625:ℝ) ∧
    standardCDF (442/625:ℝ) < 76027892/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_gaussian_exponential_integral_uniform_rational_error (442/625:ℝ) (by constructor <;> norm_num)
  have hp : (6524224518/10000000000:ℝ) < actualPolynomialIntegral (442/625:ℝ) ∧
      actualPolynomialIntegral (442/625:ℝ) < 6524224519/10000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_large_lower_certified :
    (99979649/100000000:ℝ) < standardCDF (7071/2000:ℝ) ∧
    standardCDF (7071/2000:ℝ) < 99979651/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_exponential_integral_error_through_radius_four (7071/2000:ℝ) (by constructor <;> norm_num)
  have hp : (12528040331/10000000000:ℝ) < polynomialIntegral48 (7071/2000:ℝ) ∧
      polynomialIntegral48 (7071/2000:ℝ) < 12528040332/10000000000 := by
    norm_num [polynomialIntegral48,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

theorem actual_CDF_large_upper_certified :
    (99979656/100000000:ℝ) < standardCDF (8839/2500:ℝ) ∧
    standardCDF (8839/2500:ℝ) < 99979659/100000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have he := actual_exponential_integral_error_through_radius_four (8839/2500:ℝ) (by constructor <;> norm_num)
  have hp : (12528042261/10000000000:ℝ) < polynomialIntegral48 (8839/2500:ℝ) ∧
      polynomialIntegral48 (8839/2500:ℝ) < 12528042262/10000000000 := by
    norm_num [polynomialIntegral48,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at he
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

end SafeLearning.CompleteAppliedGaussianMixtureCDFNumbers24
