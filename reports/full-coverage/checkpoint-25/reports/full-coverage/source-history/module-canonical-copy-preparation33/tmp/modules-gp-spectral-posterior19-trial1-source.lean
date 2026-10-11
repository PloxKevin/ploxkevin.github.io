import SafeLearning.CompleteModulesGPPosteriorRegularizerCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPSpectralPosterior
open CompleteModulesMatrixGP CompleteModulesGPPosteriorRegularizerCalculus

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_orthogonal_spectral_ridge_inverse
    (Q : Matrix I I ℝ) (eigenvalue : I → ℝ) (lambda : ℝ)
    (hleft : Qᵀ * Q = 1) (hright : Q * Qᵀ = 1)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hlambda : 0 < lambda) :
    (ridgeMatrix (Q * diagonal eigenvalue * Qᵀ) lambda)⁻¹ =
      Q * diagonal (fun i => (eigenvalue i + lambda)⁻¹) * Qᵀ := by
  have hd : diagonal (fun i => eigenvalue i + lambda) =
      diagonal eigenvalue + lambda • (1 : Matrix I I ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [diagonal_apply, Matrix.one_apply, hij]
  have hshift : ridgeMatrix (Q * diagonal eigenvalue * Qᵀ) lambda =
      Q * diagonal (fun i => eigenvalue i + lambda) * Qᵀ := by
    rw [hd, Matrix.mul_add, Matrix.add_mul]
    simp [ridgeMatrix, Matrix.mul_smul, Matrix.smul_mul, hright]
  have hinv : diagonal (fun i => (eigenvalue i + lambda)⁻¹) *
      diagonal (fun i => eigenvalue i + lambda) = (1 : Matrix I I ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    have hnonzero : eigenvalue i + lambda ≠ 0 := by linarith [heigenvalue i]
    by_cases hij : i = j
    · subst j
      simp [hnonzero]
    · simp [diagonal_apply, Matrix.one_apply, hij]
  apply Matrix.inv_eq_left_inv
  rw [hshift]
  calc
    (Q * diagonal (fun i => (eigenvalue i + lambda)⁻¹) * Qᵀ) *
        (Q * diagonal (fun i => eigenvalue i + lambda) * Qᵀ) =
      Q * (diagonal (fun i => (eigenvalue i + lambda)⁻¹) *
        (Qᵀ * Q) * diagonal (fun i => eigenvalue i + lambda)) * Qᵀ := by
          noncomm_ring
    _ = 1 := by rw [hleft, Matrix.mul_one, hinv, Matrix.mul_one, hright]

theorem actual_matrix_posterior_variance_equals_the_printed_spectral_sum
    (Q : Matrix I I ℝ) (eigenvalue query : I → ℝ) (queryDiagonal lambda : ℝ)
    (hleft : Qᵀ * Q = 1) (hright : Q * Qᵀ = 1)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hlambda : 0 < lambda) :
    posteriorVariance (Q * diagonal eigenvalue * Qᵀ) query queryDiagonal lambda =
      spectralVariance eigenvalue (Qᵀ *ᵥ query) queryDiagonal lambda := by
  unfold posteriorVariance spectralVariance
  rw [actual_orthogonal_spectral_ridge_inverse Q eigenvalue lambda hleft hright
    heigenvalue hlambda]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  simp only [diagonal_mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actual_matrix_spectral_posterior_variance_has_nonnegative_derivative
    (Q : Matrix I I ℝ) (eigenvalue query : I → ℝ) (queryDiagonal lambda : ℝ)
    (hleft : Qᵀ * Q = 1) (hright : Q * Qᵀ = 1)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hlambda : 0 < lambda) :
    HasDerivAt (posteriorVariance (Q * diagonal eigenvalue * Qᵀ) query queryDiagonal)
      (∑ i, ((Qᵀ *ᵥ query) i)^2 / (eigenvalue i + lambda)^2) lambda ∧
      0 ≤ ∑ i, ((Qᵀ *ᵥ query) i)^2 / (eigenvalue i + lambda)^2 := by
  constructor
  · apply (actual_spectral_posterior_variance_has_the_printed_derivative
      eigenvalue (Qᵀ *ᵥ query) queryDiagonal lambda heigenvalue hlambda).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hlambda] with l hl
    exact actual_matrix_posterior_variance_equals_the_printed_spectral_sum
      Q eigenvalue query queryDiagonal l hleft hright heigenvalue hl
  · exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

end SafeLearning.CompleteModulesGPSpectralPosterior
