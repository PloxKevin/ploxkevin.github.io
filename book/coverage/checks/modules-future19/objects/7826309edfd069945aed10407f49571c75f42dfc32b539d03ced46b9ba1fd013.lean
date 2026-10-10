import SafeLearning.CompleteModulesGPSpectralPosterior
import SafeLearning.CompleteModulesGPConfidenceComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPPosteriorPSDConsequences
open CompleteModulesMatrixGP CompleteModulesGPPosteriorRegularizerCalculus
open CompleteModulesGPSpectralPosterior CompleteModulesGPConfidenceComparison

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_arbitrary_positive_semidefinite_gram_has_the_required_nonnegative_spectral_decomposition
    (gram : Matrix I I ℝ) (hgram : gram.PosSemidef) :
    ∃ (Q : Matrix I I ℝ) (eigenvalue : I → ℝ),
      Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧ (∀ i, 0 ≤ eigenvalue i) ∧
        gram = Q * diagonal eigenvalue * Qᵀ := by
  let U := hgram.isHermitian.eigenvectorUnitary
  refine ⟨(U : Matrix I I ℝ), hgram.isHermitian.eigenvalues, ?_, ?_,
    hgram.eigenvalues_nonneg, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self U
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self U
  · simpa [U, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hgram.isHermitian.spectral_theorem

theorem actual_arbitrary_positive_semidefinite_gram_posterior_variance_is_monotone
    (gram : Matrix I I ℝ) (hgram : gram.PosSemidef) (query : I → ℝ)
    (queryDiagonal small large : ℝ) (hsmall : 0 < small) (horder : small ≤ large) :
    posteriorVariance gram query queryDiagonal small ≤
      posteriorVariance gram query queryDiagonal large := by
  obtain ⟨Q, eigenvalue, hleft, hright, heigenvalue, hdecomposition⟩ :=
    actual_arbitrary_positive_semidefinite_gram_has_the_required_nonnegative_spectral_decomposition
      gram hgram
  rw [hdecomposition,
    actual_matrix_posterior_variance_equals_the_printed_spectral_sum Q eigenvalue query
      queryDiagonal small hleft hright heigenvalue hsmall,
    actual_matrix_posterior_variance_equals_the_printed_spectral_sum Q eigenvalue query
      queryDiagonal large hleft hright heigenvalue (lt_of_lt_of_le hsmall horder)]
  exact actual_spectral_posterior_variance_is_monotone_for_positive_regularizers
    eigenvalue (Qᵀ *ᵥ query) queryDiagonal small large heigenvalue hsmall horder

theorem actual_finite_query_vector_tending_to_zero_makes_the_matrix_variance_tend_to_the_prior
    {J : Type*} (l : Filter J) (gram : Matrix I I ℝ) (query : J → I → ℝ)
    (queryDiagonal lambda : ℝ) (hquery : Tendsto query l (𝓝 0)) :
    Tendsto (fun j => posteriorVariance gram (query j) queryDiagonal lambda)
      l (𝓝 queryDiagonal) := by
  have hc : Continuous (fun q : I → ℝ => posteriorVariance gram q queryDiagonal lambda) := by
    unfold posteriorVariance Matrix.mulVec dotProduct
    fun_prop
  have ht := (hc.tendsto (0 : I → ℝ)).comp hquery
  simpa [posteriorVariance, Matrix.mulVec, dotProduct] using ht

theorem actual_finite_query_vector_tending_to_zero_makes_the_width_ratio_tend_to_the_multiplier_ratio
    {J : Type*} (l : Filter J) (gram : Matrix I I ℝ) (query : J → I → ℝ)
    (prior : ℝ) (hprior : 0 < prior) (hquery : Tendsto query l (𝓝 0)) :
    Tendsto (fun j => sourceSrinivasMultiplier *
      Real.sqrt (posteriorVariance gram (query j) prior (1 / 100)) /
        (sourceChowdhuryMultiplier *
          Real.sqrt (posteriorVariance gram (query j) prior (51 / 50))))
      l (𝓝 sourceMultiplierRatio) := by
  have hs := (actual_finite_query_vector_tending_to_zero_makes_the_matrix_variance_tend_to_the_prior
    l gram query prior (1 / 100) hquery).sqrt.const_mul sourceSrinivasMultiplier
  have hc := (actual_finite_query_vector_tending_to_zero_makes_the_matrix_variance_tend_to_the_prior
    l gram query prior (51 / 50) hquery).sqrt.const_mul sourceChowdhuryMultiplier
  have hp : 0 < sourceChowdhuryMultiplier := by
    linarith [actual_source_chowdhury_multiplier_and_noise_have_the_printed_roundings.1]
  have hd : sourceChowdhuryMultiplier * Real.sqrt prior ≠ 0 :=
    (mul_pos hp (Real.sqrt_pos.2 hprior)).ne'
  have ht := hs.div hc hd
  convert ht using 1
  rw [actual_zero_cross_covariance_makes_the_width_ratio_equal_the_multiplier_ratio prior hprior]

end SafeLearning.CompleteModulesGPPosteriorPSDConsequences
