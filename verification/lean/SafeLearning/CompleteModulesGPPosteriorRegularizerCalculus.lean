import SafeLearning.CompleteModulesMatrixGP

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPPosteriorRegularizerCalculus
open CompleteModulesMatrixGP

variable {I : Type*} [Fintype I]

def spectralVariance (eigenvalue coordinate : I → ℝ) (queryDiagonal lambda : ℝ) : ℝ :=
  queryDiagonal - ∑ i, (coordinate i)^2/(eigenvalue i+lambda)

theorem actual_spectral_posterior_variance_has_the_printed_derivative
    (eigenvalue coordinate : I → ℝ) (queryDiagonal lambda : ℝ)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hlambda : 0 < lambda) :
    HasDerivAt (spectralVariance eigenvalue coordinate queryDiagonal)
      (∑ i, (coordinate i)^2/(eigenvalue i+lambda)^2) lambda := by
  have hi (i : I) : HasDerivAt (fun l : ℝ => (coordinate i)^2/(eigenvalue i+l))
      (-(coordinate i)^2/(eigenvalue i+lambda)^2) lambda := by
    have hd : eigenvalue i+lambda ≠ 0 := by linarith [heigenvalue i]
    have h := (hasDerivAt_const lambda ((coordinate i)^2)).div
      ((hasDerivAt_const lambda (eigenvalue i)).add (hasDerivAt_id lambda)) hd
    convert h using 1
    · funext l
      rfl
    · change -(coordinate i)^2/(eigenvalue i+lambda)^2 =
        (0*(eigenvalue i+lambda)-(coordinate i)^2*(0+1))/(eigenvalue i+lambda)^2
      ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have h := (hasDerivAt_const lambda queryDiagonal).sub hs
  convert h using 1
  · rfl
  · simp only [zero_sub,← Finset.sum_neg_distrib,neg_div,neg_neg]

theorem actual_spectral_posterior_variance_derivative_is_nonnegative
    (eigenvalue coordinate : I → ℝ) (queryDiagonal lambda : ℝ)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hlambda : 0 < lambda) :
    deriv (spectralVariance eigenvalue coordinate queryDiagonal) lambda =
      (∑ i, (coordinate i)^2/(eigenvalue i+lambda)^2) ∧
      0 ≤ deriv (spectralVariance eigenvalue coordinate queryDiagonal) lambda := by
  have he := (actual_spectral_posterior_variance_has_the_printed_derivative
    eigenvalue coordinate queryDiagonal lambda heigenvalue hlambda).deriv
  refine ⟨he,?_⟩
  rw [he]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem actual_spectral_posterior_variance_is_monotone_for_positive_regularizers
    (eigenvalue coordinate : I → ℝ) (queryDiagonal small large : ℝ)
    (heigenvalue : ∀ i, 0 ≤ eigenvalue i) (hsmall : 0 < small) (horder : small ≤ large) :
    spectralVariance eigenvalue coordinate queryDiagonal small ≤
      spectralVariance eigenvalue coordinate queryDiagonal large := by
  unfold spectralVariance
  have heach (i : I) : (coordinate i)^2/(eigenvalue i+large) ≤
      (coordinate i)^2/(eigenvalue i+small) := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [heigenvalue i])
      (by linarith)
  have hs : (∑ i, (coordinate i)^2/(eigenvalue i+large)) ≤
      ∑ i, (coordinate i)^2/(eigenvalue i+small) :=
    Finset.sum_le_sum (fun i _ => heach i)
  linarith

theorem actual_single_point_matrix_posterior_variance_is_the_source_formula
    (cross lambda : ℝ) (hlambda : 0 < lambda) :
    posteriorVariance (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => cross) 1 lambda =
      1-cross^2/(1+lambda) := by
  have hden : 1+lambda ≠ 0 := by linarith
  have hu : IsUnit (ridgeMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) lambda).det := by
    simp only [ridgeMatrix,Matrix.det_fin_one]
    norm_num
    exact hden
  have hsolve : ridgeMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) lambda *ᵥ
      (fun _ => cross/(1+lambda)) = (fun _ => cross) := by
    ext i
    fin_cases i
    simp [ridgeMatrix,Matrix.mulVec,dotProduct]
    field_simp [hden]
  have hinv := regularized_solve_is_inverse_solution
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => cross) (fun _ => cross/(1+lambda))
    lambda hu hsolve
  simp only [posteriorVariance,hinv,dotProduct,Fin.sum_univ_one]
  ring

theorem actual_observed_and_zero_cross_covariance_source_variance_examples :
    posteriorVariance (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) 1 (1/100) = 1/101 ∧
      posteriorVariance (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) 1 (51/50) = 51/101 ∧
      ∀ lambda : ℝ, 0 < lambda →
        posteriorVariance (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 0) 1 lambda = 1 := by
  constructor
  · rw [actual_single_point_matrix_posterior_variance_is_the_source_formula _ _ (by norm_num)]
    norm_num
  constructor
  · rw [actual_single_point_matrix_posterior_variance_is_the_source_formula _ _ (by norm_num)]
    norm_num
  · intro lambda hlambda
    rw [actual_single_point_matrix_posterior_variance_is_the_source_formula _ _ hlambda]
    simp

theorem actual_latent_unit_variance_covariance_is_positive_semidefinite
    (cross : ℝ) (hcross : |cross| ≤ 1) :
    ( !![1,cross;cross,1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro v
    have hs : 0 ≤ 1-cross^2 := by
      have hab := abs_le.mp hcross
      nlinarith [sq_nonneg cross]
    have h := add_nonneg (sq_nonneg (v 0+cross*v 1)) (mul_nonneg hs (sq_nonneg (v 1)))
    convert h using 1
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two]
    ring

end SafeLearning.CompleteModulesGPPosteriorRegularizerCalculus
