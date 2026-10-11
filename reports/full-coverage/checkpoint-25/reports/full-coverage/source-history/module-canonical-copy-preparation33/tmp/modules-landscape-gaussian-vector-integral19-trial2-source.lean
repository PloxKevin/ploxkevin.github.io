import SafeLearning.CompleteModulesLandscapeGaussianQuadraticIntegral

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeGaussianVectorIntegral
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace NNReal
open CompleteModulesLandscapeGaussianQuadraticIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual isotropic Gaussian with coordinate variance a, defined using
independent scalar Gaussian coordinates rather than an asserted integral law. -/
def actualIsotropicGaussian (a : ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 a)).map (toLp 2)

/-- Scalar Gaussian dilation and the true product map derive the isotropic
prior from a scaled standard Gaussian, including variance zero. -/
theorem actual_isotropic_gaussian_is_the_scaled_standard_gaussian (a : ℝ≥0) :
    actualIsotropicGaussian (ι := ι) a =
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun theta => Real.sqrt (a : ℝ) • theta) := by
  have hg : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (a : ℝ) * x) = gaussianReal 0 a := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [Real.sq_sqrt a.coe_nonneg]
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun theta : EuclideanSpace ℝ ι => Real.sqrt (a : ℝ) • theta) ∘ toLp 2 =
      (toLp 2) ∘ (fun x : ι → ℝ => fun i => Real.sqrt (a : ℝ) * x i) := by
    ext x i
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.pi_map_pi (fun _ => by fun_prop)]
  simp_rw [hg]
  rfl

private theorem actual_scaled_quadratic_tilt
    (a : ℝ≥0) (V : Matrix ι ι ℝ) (S theta : EuclideanSpace ℝ ι) :
    actualQuadraticGaussianTilt V S (Real.sqrt (a : ℝ) • theta) =
      actualQuadraticGaussianTilt ((a : ℝ) • V) (Real.sqrt (a : ℝ) • S) theta := by
  unfold actualQuadraticGaussianTilt
  simp only [map_smul, smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  congr 1
  have hh := congrArg (fun r : ℝ => r * ⟪theta, toEuclideanCLM (𝕜 := ℝ) V theta⟫)
    (Real.sq_sqrt a.coe_nonneg)
  nlinarith

/-- Actual integrability for the finite isotropic Gaussian and every PSD
quadratic, obtained by dilation of the already computed standard integral. -/
theorem actual_isotropic_psd_gaussian_quadratic_exponential_is_integrable
    (a : ℝ≥0) (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) :
    Integrable (actualQuadraticGaussianTilt V S) (actualIsotropicGaussian a) := by
  rw [actual_isotropic_gaussian_is_the_scaled_standard_gaussian]
  apply (integrable_map_measure (by unfold actualQuadraticGaussianTilt; fun_prop)
    (Measurable.aemeasurable (by fun_prop))).mpr
  simpa only [Function.comp_def, actual_scaled_quadratic_tilt] using
    actual_psd_standard_gaussian_quadratic_exponential_is_integrable ((a : ℝ) • V)
      (hV.smul a.coe_nonneg) (Real.sqrt (a : ℝ) • S)

/-- The actual finite-vector Gaussian quadratic integral for any prior
variance a. The determinant and inverse are the actual normalized matrix. -/
theorem actual_isotropic_psd_gaussian_quadratic_integral_has_the_exact_determinant_value
    (a : ℝ≥0) (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) :
    (∫ theta, actualQuadraticGaussianTilt V S theta ∂actualIsotropicGaussian a) =
      (Real.sqrt (1 + (a : ℝ) • V).det)⁻¹ *
        Real.exp ((a : ℝ) / 2 * ⟪S, toEuclideanCLM (𝕜 := ℝ) (1 + (a : ℝ) • V)⁻¹ S⟫) := by
  rw [actual_isotropic_gaussian_is_the_scaled_standard_gaussian,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by unfold actualQuadraticGaussianTilt; fun_prop))]
  simp_rw [actual_scaled_quadratic_tilt]
  rw [actual_psd_standard_gaussian_quadratic_integral_has_the_exact_determinant_value
    ((a : ℝ) • V) (hV.smul a.coe_nonneg) (Real.sqrt (a : ℝ) • S)]
  congr 2
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  have hh := congrArg (fun r : ℝ => r *
    ⟪S, toEuclideanCLM (𝕜 := ℝ) (1 + (a : ℝ) • V)⁻¹ S⟫) (Real.sq_sqrt a.coe_nonneg)
  nlinarith

private theorem actual_coordinate_quadratic_tilt
    (V : Matrix ι ι ℝ) (S theta : ι → ℝ) :
    actualQuadraticGaussianTilt V (toLp 2 S) (toLp 2 theta) =
      Real.exp (theta ⬝ᵥ S - theta ⬝ᵥ (V *ᵥ theta) / 2) := by
  unfold actualQuadraticGaussianTilt
  rw [inner_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Direct finite-function product-Gaussian integrability, suitable for
mixing predictable finite-feature exponential processes. -/
theorem actual_finite_coordinate_psd_gaussian_quadratic_exponential_is_integrable
    (a : ℝ≥0) (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : ι → ℝ) :
    Integrable (fun theta : ι → ℝ => Real.exp (theta ⬝ᵥ S - theta ⬝ᵥ (V *ᵥ theta) / 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 a)) := by
  have hi := actual_isotropic_psd_gaussian_quadratic_exponential_is_integrable a V hV (toLp 2 S)
  rw [actualIsotropicGaussian] at hi
  have hc := (integrable_map_measure hi.aestronglyMeasurable
    (Measurable.aemeasurable (by fun_prop))).mp hi
  simpa only [Function.comp_def, actual_coordinate_quadratic_tilt] using hc

/-- Direct finite-coordinate determinant/inverse-quadratic integral. No
distinct-coordinate, invertible PSD, or positive-dimension assumption is used. -/
theorem actual_finite_coordinate_psd_gaussian_quadratic_integral_has_the_exact_determinant_value
    (a : ℝ≥0) (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : ι → ℝ) :
    (∫ theta : ι → ℝ, Real.exp (theta ⬝ᵥ S - theta ⬝ᵥ (V *ᵥ theta) / 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 a)) =
      (Real.sqrt (1 + (a : ℝ) • V).det)⁻¹ *
        Real.exp ((a : ℝ) / 2 * (S ⬝ᵥ ((1 + (a : ℝ) • V)⁻¹ *ᵥ S))) := by
  have he := actual_isotropic_psd_gaussian_quadratic_integral_has_the_exact_determinant_value
    a V hV (toLp 2 S)
  rw [actualIsotropicGaussian,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by unfold actualQuadraticGaussianTilt; fun_prop))] at he
  simpa only [actual_coordinate_quadratic_tilt, inner_toEuclideanCLM] using he

end SafeLearning.CompleteModulesLandscapeGaussianVectorIntegral
