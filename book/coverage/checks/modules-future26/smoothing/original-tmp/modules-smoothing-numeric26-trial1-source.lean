import SafeLearning.CompleteAppliedGaussianQuantile
import SafeLearning.CompleteFoundationsNormDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesSmoothingNumeric26
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianGeneralIntegral CompleteFoundationsNormDuality

def trueGaussianQuantile (probability : ℝ) : ℝ :=
  sInf {point : ℝ | probability ≤ standardCDF point}

theorem actual_true_quantile_at_every_cdf_value (point : ℝ) :
    trueGaussianQuantile (standardCDF point) = point ∧
    (∀ other, standardCDF point ≤ standardCDF other ↔ point ≤ other) := by
  have hm := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hs : {other : ℝ | standardCDF point ≤ standardCDF other} = Ici point := by
    ext other
    simpa using hm.le_iff_le
  exact ⟨by rw [trueGaussianQuantile, hs, csInf_Ici], fun other => hm.le_iff_le⟩

theorem actual_literal_gaussian_inverse_and_radii :
    trueGaussianQuantile (standardCDF 2) = 2 ∧
    standardCDF 0 = 1/2 ∧ trueGaussianQuantile (1/2) = 0 ∧
    (1/2 : ℝ) * trueGaussianQuantile (standardCDF 2) = 1 ∧
    (1/2 : ℝ) * trueGaussianQuantile (1/2) = 0 := by
  have htwo := (actual_true_quantile_at_every_cdf_value 2).1
  have hzero := (actual_true_quantile_at_every_cdf_value 0).1
  rw [actual_standard_gaussian_symmetry_and_half_mass] at hzero
  exact ⟨htwo,actual_standard_gaussian_symmetry_and_half_mass,hzero,
    by rw [htwo]; norm_num,by rw [hzero]; norm_num⟩

theorem actual_phi_two_nine_decimal_rounding :
    (97724986804/100000000000 : ℝ) < standardCDF 2 ∧
    standardCDF 2 < (97724986806/100000000000 : ℝ) ∧
    |standardCDF 2 - (977249868/1000000000 : ℝ)| < 1/2000000000 := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have hi := actual_gaussian_exponential_integral_uniform_rational_error
    2 (by norm_num)
  have hp : (1196288013322/1000000000000 : ℝ) < actualPolynomialIntegral 2 ∧
      actualPolynomialIntegral 2 < (1196288013323/1000000000000 : ℝ) := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at hi
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · rw [abs_lt]; constructor <;> nlinarith

def certifyRadius (sigma lower : ℝ) : Option ℝ :=
  if (1/2 : ℝ) < lower then some (sigma * trueGaussianQuantile lower) else none

theorem actual_literal_certify_and_abstention :
    certifyRadius (1/2) (standardCDF 2) = some 1 ∧
    certifyRadius (1/2) (1/2) = none ∧
    ¬ ∃ radius : ℝ, 0 < radius ∧ certifyRadius (1/2) (1/2) = some radius := by
  have hp : (1/2 : ℝ) < standardCDF 2 := by
    rw [← actual_standard_gaussian_symmetry_and_half_mass]
    exact actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
      (by norm_num : (0:ℝ)<2)
  simp [certifyRadius,hp,actual_literal_gaussian_inverse_and_radii.2.2.2.1]

theorem actual_dimension_one_hundred_norm_bound (delta : Fin 100 → ℝ) :
    l2Norm delta ≤ 10 * ‖delta‖ := by
  have hb := actual_infinity_ball_in_euclidean_ball delta ‖delta‖ (norm_nonneg _) le_rfl
  norm_num at hb
  exact hb

theorem actual_strict_infinity_radius_implies_strict_euclidean_radius
    (delta : Fin 100 → ℝ) (hdelta : ‖delta‖ < (1/10:ℝ)) :
    l2Norm delta < 1 := by
  have hb := actual_dimension_one_hundred_norm_bound delta
  linarith

theorem actual_boundary_constant_vector_is_excluded :
    ‖(fun _ : Fin 100 => (1/10:ℝ))‖ = 1/10 ∧
    l2Norm (fun _ : Fin 100 => (1/10:ℝ)) = 1 ∧
    ¬ l2Norm (fun _ : Fin 100 => (1/10:ℝ)) < 1 := by
  have he := actual_constant_vector_attains_dimension_conversion
    (n:=Fin 100) (1/10:ℝ) (by norm_num)
  norm_num at he
  exact ⟨by simp,he,by rw [he]; norm_num⟩

end SafeLearning.CompleteModulesSmoothingNumeric26
