import SafeLearning.CompleteModulesLandscapeGaussianGPRegularization
import SafeLearning.CompleteModulesLandscapeGaussianQuadraticIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSmallInformationPSD
open Matrix
open scoped BigOperators RealInnerProductSpace
open CompleteModulesSafeOptFiniteInformationBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem one_add_sum_le_product (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (s : Finset ι) : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hs : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg (fun j _ => hf j)
    have hp := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 + f i by linarith [hf i])
    nlinarith [mul_nonneg (hf i) hs]

/-- Actual PSD trace is bounded by the determinant increment. The proof
uses its official nonnegative eigenvalues, also in dimension zero. -/
theorem actual_psd_normalized_trace_is_at_most_determinant_minus_one
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (a : ℝ) (ha : 0 ≤ a) :
    (a • A).trace ≤ (1 + a • A).det - 1 := by
  have hp := one_add_sum_le_product (fun i => a * hA.isHermitian.eigenvalues i)
    (fun i => mul_nonneg ha (hA.eigenvalues_nonneg i)) Finset.univ
  rw [← (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    A hA a ha).1] at hp
  have ht : (a • A).trace = ∑ i, a * hA.isHermitian.eigenvalues i := by
    rw [Matrix.trace_smul, hA.isHermitian.trace_eq_sum_eigenvalues]
    simp [Finset.mul_sum]
  rw [← ht] at hp
  linarith

/-- The true normalized log determinant is at most the true normalized
trace, by summing log(1+x) ≤ x over the derived nonnegative spectrum. -/
theorem actual_psd_normalized_logdet_is_at_most_normalized_trace
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (a : ℝ) (ha : 0 ≤ a) :
    Real.log (1 + a • A).det ≤ (a • A).trace := by
  rw [(actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    A hA a ha).1, Real.log_prod (fun i _ =>
      (show 0 < 1 + a * hA.isHermitian.eigenvalues i by
        exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha (hA.eigenvalues_nonneg i))).ne')]
  have ht : (a • A).trace = ∑ i, a * hA.isHermitian.eigenvalues i := by
    rw [Matrix.trace_smul, hA.isHermitian.trace_eq_sum_eigenvalues]
    simp [Finset.mul_sum]
  rw [ht]
  apply Finset.sum_le_sum
  intro i _
  have h := Real.log_le_sub_one_of_pos
    (show 0 < 1 + a * hA.isHermitian.eigenvalues i by
      exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha (hA.eigenvalues_nonneg i)))
  linarith

/-- Small actual PSD information forces a dimension-free trace bound. -/
theorem actual_small_psd_logdet_implies_normalized_trace_at_most_four_gamma
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda gamma : ℝ)
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (hgamma_half : gamma ≤ 1 / 2)
    (hsmall : Real.log (1 + lambda⁻¹ • A).det ≤ 2 * gamma) :
    (lambda⁻¹ • A).trace ≤ 4 * gamma := by
  have hdet := (actual_positive_semidefinite_normalized_determinant_is_a_positive_spectral_product
    A hA lambda⁻¹ (inv_nonneg.mpr hlambda.le)).2
  have hdpos : 0 < (1 + lambda⁻¹ • A).det := lt_of_lt_of_le zero_lt_one hdet
  have he := Real.exp_le_exp.mpr hsmall
  rw [Real.exp_log hdpos] at he
  have heapprox := Real.abs_exp_sub_one_le (x := 2 * gamma)
    (show |2 * gamma| ≤ 1 by rw [abs_of_pos (by positivity)]; linarith)
  rw [abs_of_pos (show 0 < 2 * gamma by positivity)] at heapprox
  have heupper := (le_abs_self (Real.exp (2 * gamma) - 1)).trans heapprox
  have ht := actual_psd_normalized_trace_is_at_most_determinant_minus_one
    A hA lambda⁻¹ (inv_nonneg.mpr hlambda.le)
  linarith

/-- Rescaling the actual regularization by small information leaves a
uniform log-determinant budget of four. -/
theorem actual_small_psd_logdet_implies_gamma_regularized_logdet_at_most_four
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda gamma : ℝ)
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (hgamma_half : gamma ≤ 1 / 2)
    (hsmall : Real.log (1 + lambda⁻¹ • A).det ≤ 2 * gamma) :
    Real.log (1 + (lambda * gamma)⁻¹ • A).det ≤ 4 := by
  have ht := actual_small_psd_logdet_implies_normalized_trace_at_most_four_gamma
    A hA lambda gamma hlambda hgamma hgamma_half hsmall
  have hscale : ((lambda * gamma)⁻¹ • A).trace =
      (lambda⁻¹ • A).trace / gamma := by
    simp only [Matrix.trace_smul, smul_eq_mul, div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hlog := actual_psd_normalized_logdet_is_at_most_normalized_trace
    A hA (lambda * gamma)⁻¹ (inv_nonneg.mpr (mul_pos hlambda hgamma).le)
  rw [hscale] at hlog
  exact hlog.trans ((div_le_iff₀ hgamma).mpr (by nlinarith))

private theorem actual_regularized_inverse_eigenbasis_action
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda : ℝ) (hlambda : 0 < lambda) (i : ι) :
    toEuclideanCLM (𝕜 := ℝ) (lambda • 1 + A)⁻¹ (hA.isHermitian.eigenvectorBasis i) =
      (lambda + hA.isHermitian.eigenvalues i)⁻¹ • hA.isHermitian.eigenvectorBasis i := by
  have hp : (lambda • (1 : Matrix ι ι ℝ) + A).PosDef :=
    (Matrix.PosDef.one.smul hlambda).add_posSemidef hA
  have hu : IsUnit (lambda • (1 : Matrix ι ι ℝ) + A).det :=
    isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  have he : (lambda • 1 + A) *ᵥ ⇑(hA.isHermitian.eigenvectorBasis i) =
      (lambda + hA.isHermitian.eigenvalues i) • ⇑(hA.isHermitian.eigenvectorBasis i) := by
    rw [add_mulVec, smul_mulVec, one_mulVec, hA.isHermitian.mulVec_eigenvectorBasis]
    ext j
    simp
    ring
  have hh := congrArg (fun x : ι → ℝ => (lambda • 1 + A)⁻¹ *ᵥ x) he
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_smul] at hh
  have hn : lambda + hA.isHermitian.eigenvalues i ≠ 0 :=
    (add_pos_of_pos_of_nonneg hlambda (hA.eigenvalues_nonneg i)).ne'
  have hh' := congrArg (fun x : ι → ℝ => (lambda + hA.isHermitian.eigenvalues i)⁻¹ • x) hh
  simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at hh'
  ext j
  exact congrFun hh'.symm j

/-- The true regularized inverse quadratic is diagonal in the actual
matrix's derived orthonormal eigenbasis; no spectral premise is supplied. -/
theorem actual_psd_regularized_inverse_quadratic_has_the_exact_spectral_sum
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda : ℝ) (hlambda : 0 < lambda)
    (S : EuclideanSpace ℝ ι) :
    ⟪S, toEuclideanCLM (𝕜 := ℝ) (lambda • 1 + A)⁻¹ S⟫ =
      ∑ i, ⟪hA.isHermitian.eigenvectorBasis i, S⟫ ^ 2 /
        (lambda + hA.isHermitian.eigenvalues i) := by
  let b := hA.isHermitian.eigenvectorBasis
  have hi : toEuclideanCLM (𝕜 := ℝ) (lambda • 1 + A)⁻¹ S =
      ∑ i, (⟪b i, S⟫ / (lambda + hA.isHermitian.eigenvalues i)) • b i := by
    calc
      _ = toEuclideanCLM (𝕜 := ℝ) (lambda • 1 + A)⁻¹ (∑ i, ⟪b i, S⟫ • b i) := by rw [b.sum_repr']
      _ = _ := by
        simp only [map_sum, map_smul, b, actual_regularized_inverse_eigenbasis_action A hA lambda hlambda,
          smul_smul, div_eq_mul_inv]
  rw [hi, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, real_inner_comm S (b i)]
  dsimp only [b]
  ring

/-- Small actual information compares the actual inverse quadratics at
lambda and lambda*gamma, with the precise five-gamma factor. -/
theorem actual_small_psd_logdet_implies_actual_inverse_quadratic_comparison
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda gamma : ℝ)
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (hgamma_half : gamma ≤ 1 / 2)
    (hsmall : Real.log (1 + lambda⁻¹ • A).det ≤ 2 * gamma) (S : ι → ℝ) :
    S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S) ≤
      5 * gamma * (S ⬝ᵥ (((lambda * gamma) • 1 + A)⁻¹ *ᵥ S)) := by
  have ht := actual_small_psd_logdet_implies_normalized_trace_at_most_four_gamma
    A hA lambda gamma hlambda hgamma hgamma_half hsmall
  have heigen : ∀ i, hA.isHermitian.eigenvalues i ≤ 4 * gamma * lambda := by
    intro i
    have hs := Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    have hsum : (∑ j, hA.isHermitian.eigenvalues j) = A.trace := by
      simpa using hA.isHermitian.trace_eq_sum_eigenvalues.symm
    rw [hsum] at hs
    rw [Matrix.trace_smul] at ht
    change lambda⁻¹ * A.trace ≤ 4 * gamma at ht
    have ht' : A.trace / lambda ≤ 4 * gamma := by simpa [div_eq_mul_inv, mul_comm] using ht
    exact hs.trans ((div_le_iff₀ hlambda).mp ht')
  have hq1 := actual_psd_regularized_inverse_quadratic_has_the_exact_spectral_sum A hA lambda hlambda (WithLp.toLp 2 S)
  have hq2 := actual_psd_regularized_inverse_quadratic_has_the_exact_spectral_sum A hA (lambda * gamma) (mul_pos hlambda hgamma) (WithLp.toLp 2 S)
  rw [inner_toEuclideanCLM] at hq1 hq2
  rw [hq1, hq2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd := hA.eigenvalues_nonneg i
  have hden1 : 0 < lambda + hA.isHermitian.eigenvalues i := add_pos_of_pos_of_nonneg hlambda hd
  have hden2 : 0 < lambda * gamma + hA.isHermitian.eigenvalues i := add_pos_of_pos_of_nonneg (mul_pos hlambda hgamma) hd
  have hden : lambda * gamma + hA.isHermitian.eigenvalues i ≤
      5 * gamma * (lambda + hA.isHermitian.eigenvalues i) := by
    nlinarith [heigen i, mul_nonneg hgamma.le hd]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hden1 hden2).mpr
  have hsquare := sq_nonneg ⟪hA.isHermitian.eigenvectorBasis i, WithLp.toLp 2 S⟫
  nlinarith [mul_le_mul_of_nonneg_left hden hsquare]

end SafeLearning.CompleteModulesLandscapeSmallInformationPSD
