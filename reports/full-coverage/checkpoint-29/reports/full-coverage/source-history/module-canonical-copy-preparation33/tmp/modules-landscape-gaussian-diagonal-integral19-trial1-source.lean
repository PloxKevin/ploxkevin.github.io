import SafeLearning.CompleteModulesLandscapeScalarGaussianMixture

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeGaussianDiagonalIntegral
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open CompleteModulesLandscapeScalarGaussianMixture

/-- Actual product-Gaussian integrability for a nonnegative diagonal quadratic,
including the empty coordinate space. -/
theorem actual_finite_diagonal_gaussian_quadratic_exponential_is_integrable
    {ι : Type*} [Fintype ι] (a : ℝ≥0) (v s : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Integrable (fun x : ι → ℝ => Real.exp (∑ i, (x i * s i - v i * (x i) ^ 2 / 2)))
      (Measure.pi (fun _ : ι => gaussianReal 0 a)) := by
  simpa only [Real.exp_sum] using
    Integrable.fintype_prod (fun i =>
      actual_nonnegative_quadratic_gaussian_tilt_mixture_is_integrable a (v i) (s i) (hv i))

/-- The finite product integral is computed from the genuine scalar density
identity. Its factors combine into the diagonal determinant and inverse quadratic. -/
theorem actual_finite_diagonal_gaussian_quadratic_integral_has_the_exact_product_value
    {ι : Type*} [Fintype ι] (a : ℝ≥0) (ha : 0 < a)
    (v s : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∫ x : ι → ℝ, Real.exp (∑ i, (x i * s i - v i * (x i) ^ 2 / 2))
      ∂Measure.pi (fun _ : ι => gaussianReal 0 a)) =
      (Real.sqrt (∏ i, (1 + (a : ℝ) * v i)))⁻¹ *
        Real.exp ((a : ℝ) / 2 * ∑ i, (s i) ^ 2 / (1 + (a : ℝ) * v i)) := by
  classical
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod]
  simp_rw [actual_gaussian_tilt_integral_is_the_exact_scalar_self_normalized_value a ha _ _ (hv _),
    mixtureValue]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    ← Real.sqrt_prod _ (fun i _ => by positivity), ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SafeLearning.CompleteModulesLandscapeGaussianDiagonalIntegral
