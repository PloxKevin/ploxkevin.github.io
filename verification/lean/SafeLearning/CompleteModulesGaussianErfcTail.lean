import SafeLearning.CompleteAppliedGaussianCDF
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace SafeLearning.CompleteModulesGaussianErfcTail
open CompleteAppliedGaussianCDF

def erfc (a : ℝ) : ℝ := 2*(Real.sqrt Real.pi)⁻¹*(∫s in Ioi a, Real.exp (-s^2))
def upperTail (z : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi z)

theorem actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral (z : ℝ) :
    upperTail z = 1-standardCDF z ∧
      upperTail z = (Real.sqrt (2*Real.pi))⁻¹*(∫x in Ioi z, Real.exp (-x^2/2)) := by
  constructor
  · have h := measureReal_compl (μ := gaussianReal 0 1) (s := Iic z) measurableSet_Iic
    simpa [upperTail, standardCDF] using h
  · rw [upperTail, Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num), ENNReal.toReal_ofReal]
    · have he : gaussianPDFReal 0 1 = fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
        funext x; simp [gaussianPDFReal]
      rw [he, integral_const_mul]
    · exact integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _)

theorem actual_density_change_of_variable_gives_the_complementary_error_function (z : ℝ) :
    upperTail z = (Real.sqrt Real.pi)⁻¹*(∫s in Ioi (z/Real.sqrt 2), Real.exp (-s^2)) ∧
      upperTail z = (1/2:ℝ)*erfc (z/Real.sqrt 2) := by
  have hs : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsq : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsub := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x^2/2)) (z/Real.sqrt 2) hs
  have he : (fun s : ℝ => Real.exp (-(Real.sqrt 2*s)^2/2)) = fun s => Real.exp (-s^2) := by
    funext s
    congr 1
    rw [mul_pow, hsq]
    ring
  have hz : Real.sqrt 2*(z/Real.sqrt 2) = z := by field_simp
  rw [he, hz] at hsub
  simp only [smul_eq_mul] at hsub
  have hnormal : Real.sqrt (2*Real.pi) = Real.sqrt 2*Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi
  have h := (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral z).2
  rw [hnormal, mul_inv_rev] at h
  have htail : upperTail z = (Real.sqrt Real.pi)⁻¹*(∫s in Ioi (z/Real.sqrt 2), Real.exp (-s^2)) := by
    rw [hsub]
    simpa only [mul_assoc] using h
  exact ⟨htail, by rw [htail, erfc]; ring⟩

theorem actual_complementary_error_function_uses_a_genuine_improper_integral (a : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s^2)) (Ioi a) ∧
    Tendsto (fun b : ℝ => 2*(Real.sqrt Real.pi)⁻¹*(∫s in a..b, Real.exp (-s^2)))
      atTop (𝓝 (erfc a)) := by
  have hi : Integrable (fun s : ℝ => Real.exp (-s^2)) := by
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1))
  refine ⟨hi.integrableOn, ?_⟩
  exact (intervalIntegral_tendsto_integral_Ioi a hi.integrableOn tendsto_id).const_mul _

theorem actual_zero_tail_has_half_mass_and_erfc_zero_is_one :
    upperTail 0 = 1/2 ∧ erfc 0 = 1 := by
  have h := (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral 0).1
  rw [actual_standard_gaussian_symmetry_and_half_mass] at h
  have he := (actual_density_change_of_variable_gives_the_complementary_error_function 0).2
  simp only [zero_div] at he
  constructor <;> linarith

theorem actual_gaussian_upper_tail_is_positive_at_every_finite_threshold (z : ℝ) :
    0 < upperTail z := by
  have hn : (gaussianReal 0 1) (Ioi z) ≠ 0 := by
    intro hzero
    have hv := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0) hzero
    simp only [Real.volume_Ioi] at hv
    exact ENNReal.top_ne_zero hv
  exact ENNReal.toReal_pos hn (measure_ne_top _ _)

end SafeLearning.CompleteModulesGaussianErfcTail
