import SafeLearning.CompleteModulesLandscapeGaussianDiagonalIntegral
import SafeLearning.CompleteModulesSafeOptFiniteInformationBound

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeGaussianQuadraticIntegral
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
open CompleteModulesLandscapeGaussianDiagonalIntegral CompleteModulesSafeOptFiniteInformationBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualQuadraticGaussianTilt (V : Matrix ι ι ℝ) (S : EuclideanSpace ℝ ι)
    (theta : EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (⟪theta, S⟫ - ⟪theta, toEuclideanCLM (𝕜 := ℝ) V theta⟫ / 2)

private theorem actual_psd_eigenbasis_action
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (i : ι) :
    toEuclideanCLM (𝕜 := ℝ) V (hV.isHermitian.eigenvectorBasis i) =
      hV.isHermitian.eigenvalues i • hV.isHermitian.eigenvectorBasis i := by
  ext j
  exact congrFun (hV.isHermitian.mulVec_eigenvectorBasis i) j

private theorem actual_psd_inverse_eigenbasis_action
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (i : ι) :
    toEuclideanCLM (𝕜 := ℝ) (1 + V)⁻¹ (hV.isHermitian.eigenvectorBasis i) =
      (1 + hV.isHermitian.eigenvalues i)⁻¹ • hV.isHermitian.eigenvectorBasis i := by
  have hd := (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    V hV 1 zero_le_one).2
  simp only [one_smul] at hd
  have hu : IsUnit (1 + V).det := isUnit_iff_ne_zero.mpr (by linarith)
  have he : (1 + V) *ᵥ ⇑(hV.isHermitian.eigenvectorBasis i) =
      (1 + hV.isHermitian.eigenvalues i) • ⇑(hV.isHermitian.eigenvectorBasis i) := by
    rw [add_mulVec, one_mulVec, hV.isHermitian.mulVec_eigenvectorBasis]
    ext j
    simp
    ring
  have hh := congrArg (fun x : ι → ℝ => (1 + V)⁻¹ *ᵥ x) he
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_smul] at hh
  have hn : 1 + hV.isHermitian.eigenvalues i ≠ 0 := by
    have := hV.eigenvalues_nonneg i
    positivity
  have hh' := congrArg (fun x : ι → ℝ => (1 + hV.isHermitian.eigenvalues i)⁻¹ • x) hh
  simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at hh'
  ext j
  exact congrFun hh'.symm j

private theorem actual_psd_eigenbasis_tilt_formula
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) (x : ι → ℝ) :
    actualQuadraticGaussianTilt V S (∑ i, x i • hV.isHermitian.eigenvectorBasis i) =
      Real.exp (∑ i, (x i * ⟪hV.isHermitian.eigenvectorBasis i, S⟫ -
        hV.isHermitian.eigenvalues i * (x i) ^ 2 / 2)) := by
  let b := hV.isHermitian.eigenvectorBasis
  have haction : toEuclideanCLM (𝕜 := ℝ) V (∑ i, x i • b i) =
      ∑ i, (x i * hV.isHermitian.eigenvalues i) • b i := by
    simp only [map_sum, map_smul, b, actual_psd_eigenbasis_action, smul_smul]
  have hquad : ⟪∑ i, x i • b i, toEuclideanCLM (𝕜 := ℝ) V (∑ i, x i • b i)⟫ =
      ∑ i, hV.isHermitian.eigenvalues i * (x i) ^ 2 := by
    rw [haction, b.orthonormal.inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  unfold actualQuadraticGaussianTilt
  change Real.exp (⟪∑ i, x i • b i, S⟫ -
    ⟪∑ i, x i • b i, toEuclideanCLM (𝕜 := ℝ) V (∑ i, x i • b i)⟫ / 2) = _
  rw [hquad]
  simp only [sum_inner, real_inner_smul_left, Finset.sum_sub_distrib, Finset.sum_div, b]

/-- The actual inverse quadratic equals the diagonal inverse quadratic in
the matrix's derived orthonormal eigenbasis. -/
theorem actual_psd_normalized_inverse_quadratic_has_the_exact_spectral_sum
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) :
    ⟪S, toEuclideanCLM (𝕜 := ℝ) (1 + V)⁻¹ S⟫ =
      ∑ i, ⟪hV.isHermitian.eigenvectorBasis i, S⟫ ^ 2 /
        (1 + hV.isHermitian.eigenvalues i) := by
  let b := hV.isHermitian.eigenvectorBasis
  have hi : toEuclideanCLM (𝕜 := ℝ) (1 + V)⁻¹ S =
      ∑ i, (⟪b i, S⟫ / (1 + hV.isHermitian.eigenvalues i)) • b i := by
    calc
      _ = toEuclideanCLM (𝕜 := ℝ) (1 + V)⁻¹ (∑ i, ⟪b i, S⟫ • b i) := by rw [b.sum_repr']
      _ = _ := by
        simp only [map_sum, map_smul, b, actual_psd_inverse_eigenbasis_action,
          smul_smul, div_eq_mul_inv]
  rw [hi, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, real_inner_comm S (b i)]
  dsimp only [b]
  ring

/-- Genuine integrability for every finite-dimensional PSD quadratic tilt;
the orthonormal spectral basis is derived from the actual matrix. -/
theorem actual_psd_standard_gaussian_quadratic_exponential_is_integrable
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) :
    Integrable (actualQuadraticGaussianTilt V S) (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis hV.isHermitian.eigenvectorBasis]
  apply (integrable_map_measure (by unfold actualQuadraticGaussianTilt; fun_prop)
    (Measurable.aemeasurable (by fun_prop))).mpr
  simpa only [Function.comp_def, actual_psd_eigenbasis_tilt_formula] using
    actual_finite_diagonal_gaussian_quadratic_exponential_is_integrable 1
      hV.isHermitian.eigenvalues (fun i => ⟪hV.isHermitian.eigenvectorBasis i, S⟫)
      hV.eigenvalues_nonneg

/-- The actual standard Gaussian vector integral has the determinant and
inverse-quadratic value, including singular PSD matrices and dimension zero. -/
theorem actual_psd_standard_gaussian_quadratic_integral_has_the_exact_determinant_value
    (V : Matrix ι ι ℝ) (hV : V.PosSemidef) (S : EuclideanSpace ℝ ι) :
    (∫ theta, actualQuadraticGaussianTilt V S theta ∂stdGaussian (EuclideanSpace ℝ ι)) =
      (Real.sqrt (1 + V).det)⁻¹ * Real.exp (⟪S, toEuclideanCLM (𝕜 := ℝ) (1 + V)⁻¹ S⟫ / 2) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis hV.isHermitian.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by unfold actualQuadraticGaussianTilt; fun_prop))]
  simp_rw [actual_psd_eigenbasis_tilt_formula]
  rw [actual_finite_diagonal_gaussian_quadratic_integral_has_the_exact_product_value 1 zero_lt_one
    _ _ hV.eigenvalues_nonneg]
  have hd := (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    V hV 1 zero_le_one).1
  simp only [one_smul, NNReal.coe_one, one_mul] at hd ⊢
  rw [hd, actual_psd_normalized_inverse_quadratic_has_the_exact_spectral_sum]
  congr 2
  ring

end SafeLearning.CompleteModulesLandscapeGaussianQuadraticIntegral
