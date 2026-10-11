import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeScalarGaussianMixture
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

def mixtureVariance (a : ℝ≥0) (variance : ℝ) (hv : 0 ≤ variance) : ℝ≥0 :=
  a / ⟨1 + (a : ℝ) * variance, by positivity⟩

def mixtureMean (a : ℝ≥0) (variance sum : ℝ) : ℝ :=
  (a : ℝ) * sum / (1 + (a : ℝ) * variance)

def mixtureValue (a : ℝ≥0) (variance sum : ℝ) : ℝ :=
  (Real.sqrt (1 + (a : ℝ) * variance))⁻¹ *
    Real.exp ((a : ℝ) * sum ^ 2 / (2 * (1 + (a : ℝ) * variance)))

/-- Completing the square is a genuine equality of actual Gaussian densities,
including zero accumulated quadratic variance. -/
theorem actual_gaussian_tilt_mixture_density_has_the_completed_square_factorization
    (a : ℝ≥0) (ha : 0 < a) (variance sum tilt : ℝ) (hv : 0 ≤ variance) :
    gaussianPDFReal 0 a tilt * Real.exp (tilt * sum - variance * tilt ^ 2 / 2) =
      mixtureValue a variance sum *
        gaussianPDFReal (mixtureMean a variance sum) (mixtureVariance a variance hv) tilt := by
  have haR : (0 : ℝ) < a := NNReal.coe_pos.2 ha
  have hd : 0 < 1 + (a : ℝ) * variance := by positivity
  have hc : Real.sqrt (2 * Real.pi * (a : ℝ)) =
      Real.sqrt (1 + (a : ℝ) * variance) *
        Real.sqrt (2 * Real.pi * ((a : ℝ) / (1 + (a : ℝ) * variance))) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have he : -tilt ^ 2 / (2 * (a : ℝ)) + (tilt * sum - variance * tilt ^ 2 / 2) =
      (a : ℝ) * sum ^ 2 / (2 * (1 + (a : ℝ) * variance)) -
        (tilt - ((a : ℝ) * sum / (1 + (a : ℝ) * variance))) ^ 2 /
          (2 * ((a : ℝ) / (1 + (a : ℝ) * variance))) := by
    field_simp
    <;> ring
  simp only [gaussianPDFReal,mixtureValue,mixtureMean,mixtureVariance,NNReal.coe_div,sub_zero]
  calc
    _ = (Real.sqrt (2 * Real.pi * (a : ℝ)))⁻¹ *
        Real.exp (-tilt ^ 2 / (2 * (a : ℝ)) + (tilt * sum - variance * tilt ^ 2 / 2)) := by
      rw [Real.exp_add]
      ring
    _ = (Real.sqrt (1 + (a : ℝ) * variance) *
        Real.sqrt (2 * Real.pi * ((a : ℝ) / (1 + (a : ℝ) * variance))))⁻¹ *
        Real.exp ((a : ℝ) * sum ^ 2 / (2 * (1 + (a : ℝ) * variance)) -
          (tilt - ((a : ℝ) * sum / (1 + (a : ℝ) * variance))) ^ 2 /
            (2 * ((a : ℝ) / (1 + (a : ℝ) * variance)))) := by rw [hc,he]
    _ = _ := by
      rw [mul_inv_rev,Real.exp_sub]
      ring

/-- The true tilt mixture is integrable: nonnegative quadratic variance makes
it dominated by the genuine Gaussian linear exponential moment. -/
theorem actual_nonnegative_quadratic_gaussian_tilt_mixture_is_integrable
    (a : ℝ≥0) (variance sum : ℝ) (hv : 0 ≤ variance) :
    Integrable (fun tilt => Real.exp (tilt * sum - variance * tilt ^ 2 / 2)) (gaussianReal 0 a) := by
  have hi : Integrable (fun tilt : ℝ => Real.exp (sum * tilt)) (gaussianReal 0 a) :=
    integrable_exp_mul_gaussianReal sum
  apply hi.mono' (by fun_prop)
  filter_upwards [] with tilt
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg tilt]

/-- The actual Gaussian integral equals the scalar self-normalizing mixture
value; it is a determinant-style scalar identity, not a probability bound. -/
theorem actual_gaussian_tilt_integral_is_the_exact_scalar_self_normalized_value
    (a : ℝ≥0) (ha : 0 < a) (variance sum : ℝ) (hv : 0 ≤ variance) :
    (∫ tilt, Real.exp (tilt * sum - variance * tilt ^ 2 / 2) ∂gaussianReal 0 a) =
      mixtureValue a variance sum := by
  have hp : mixtureVariance a variance hv ≠ 0 := by unfold mixtureVariance; positivity
  rw [integral_gaussianReal_eq_integral_smul ha.ne']
  simp only [smul_eq_mul]
  simp_rw [actual_gaussian_tilt_mixture_density_has_the_completed_square_factorization a ha variance sum _ hv]
  rw [integral_const_mul,integral_gaussianPDFReal_eq_one _ hp,mul_one]

end SafeLearning.CompleteModulesLandscapeScalarGaussianMixture
