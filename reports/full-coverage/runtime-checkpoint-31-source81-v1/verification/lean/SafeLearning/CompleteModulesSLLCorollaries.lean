import SafeLearning.CompleteModulesSLLGershgorin
import SafeLearning.CompleteModulesSLLRegularization

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSLLCorollaries
open CompleteModulesSLL CompleteModulesSLLGershgorin CompleteModulesSLLRegularization

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M]

theorem actual_gershgorin_disc_for_any_normed_field {K : Type*} [NormedField K]
    (matrix : Matrix N N K) (eigenvalue : K)
    (heigen : Module.End.HasEigenvalue (Matrix.toLin' matrix) eigenvalue) :
    ∃ row,eigenvalue ∈ Metric.closedBall (matrix row row)
      (∑ column ∈ Finset.univ.erase row,‖matrix row column‖) :=
  eigenvalue_mem_ball heigen

theorem actual_source_positive_scaling_matrix_inverse
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    (Matrix.diagonal (fun coordinate => 1/scale coordinate))⁻¹=Matrix.diagonal scale :=
  Matrix.inv_eq_left_inv (actual_positive_scaling_inverse_product scale hscale)

theorem actual_source_diagonal_similarity_identity
    (gram : Matrix N N ℝ) (diagonal scale : N → ℝ)
    (hscale : ∀ coordinate,0 < scale coordinate) :
    actualSourceSimilarity (Matrix.diagonal diagonal-gram) scale=
      Matrix.diagonal diagonal-Matrix.diagonal (fun coordinate => 1/scale coordinate)*gram*
        (Matrix.diagonal (fun coordinate => 1/scale coordinate))⁻¹ := by
  rw [actual_source_positive_scaling_matrix_inverse scale hscale]
  ext row column
  rw [actual_source_similarity_entry]
  simp only [Matrix.sub_apply]
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [Matrix.diagonal_apply]
  by_cases he : row=column
  · subst column
    simp only [if_true]
    field_simp [(hscale row).ne']
  · simp [he]
    ring

theorem actual_source_gershgorin_disc_real_interval
    (symmetric : Matrix N N ℝ) (hdiagonal : ∀ coordinate,0 ≤ symmetric coordinate coordinate)
    (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) (row : N) (value : ℝ) :
    value ∈ Metric.closedBall
      (actualSourceSimilarity (CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric) scale row row)
      (∑ column ∈ Finset.univ.erase row,
        ‖actualSourceSimilarity (CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric) scale row column‖)
      ↔ value ∈ Set.Icc 0
        (2*actualSourceSimilarity (CompleteModulesScaledGram.actualScaledMajorizer symmetric scale-symmetric) scale row row) := by
  rw [actual_source_majorizer_similarity_is_diagonally_dominant symmetric hdiagonal scale hscale row,
    mem_closedBall_iff_norm,Real.norm_eq_abs,abs_le,Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem actual_standard_activations_have_unit_interval_chords
    (activation : ℝ → ℝ)
    (hactivation : activation ∈ ({(fun value : ℝ => max value 0),Real.tanh,Real.sigmoid} : Set (ℝ → ℝ))) :
    CompleteModulesLipSDP.slopeRestricted activation 0 1 := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hactivation
  rcases hactivation with h | h | h
  · subst activation
    exact CompleteModulesLipSDP.relu_slope_restricted
  · subst activation
    exact actual_tanh_has_unit_interval_chords
  · subst activation
    exact actual_sigmoid_has_unit_interval_chords

theorem actual_positive_diagonal_gram_similarity_has_source_diagonal
    (weights : Matrix M N ℝ) (diagonal scale : N → ℝ)
    (hscale : ∀ coordinate,0 < scale coordinate) (coordinate : N) :
    actualSourceSimilarity (Matrix.diagonal diagonal-weightsᵀ*weights) scale coordinate coordinate=
      diagonal coordinate-(weightsᵀ*weights) coordinate coordinate := by
  rw [actual_source_similarity_entry]
  simp only [Matrix.sub_apply,Matrix.diagonal_apply]
  simp [(hscale coordinate).ne']

theorem actual_positive_similarity_centers_force_positive_diagonal
    (weights : Matrix M N ℝ) (diagonal scale : N → ℝ)
    (hscale : ∀ coordinate,0 < scale coordinate)
    (hcenters : ∀ coordinate,0 < actualSourceSimilarity
      (Matrix.diagonal diagonal-weightsᵀ*weights) scale coordinate coordinate) :
    ∀ coordinate,0 < diagonal coordinate := by
  intro coordinate
  have hg : 0 ≤ (weightsᵀ*weights) coordinate coordinate := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hc := hcenters coordinate
  rw [actual_positive_diagonal_gram_similarity_has_source_diagonal weights diagonal scale hscale] at hc
  linarith

theorem actual_source_scaled_diagonal_dominance_implies_gram_certificate
    (weights : Matrix M N ℝ) (diagonal scale : N → ℝ)
    (hscale : ∀ coordinate,0 < scale coordinate)
    (hdominant : ∀ row,
      (∑ column ∈ Finset.univ.erase row,
        ‖actualSourceSimilarity (Matrix.diagonal diagonal-weightsᵀ*weights) scale row column‖) ≤
      actualSourceSimilarity (Matrix.diagonal diagonal-weightsᵀ*weights) scale row row) :
    (Matrix.diagonal diagonal-weightsᵀ*weights).PosSemidef := by
  have hh : (Matrix.diagonal diagonal-weightsᵀ*weights).IsHermitian := by
    change (Matrix.diagonal diagonal-weightsᵀ*weights)ᵀ=_
    simp [Matrix.transpose_mul]
  exact actual_similarity_row_dominance_implies_positive_semidefinite _ hh scale hscale hdominant

theorem actual_source_gershgorin_hypotheses_certify_relu_tanh_sigmoid_sll
    (weights : Matrix M N ℝ) (diagonal scale : N → ℝ)
    (hscale : ∀ coordinate,0 < scale coordinate)
    (hcenters : ∀ coordinate,0 < actualSourceSimilarity
      (Matrix.diagonal diagonal-weightsᵀ*weights) scale coordinate coordinate)
    (hdominant : ∀ row,
      (∑ column ∈ Finset.univ.erase row,
        ‖actualSourceSimilarity (Matrix.diagonal diagonal-weightsᵀ*weights) scale row column‖) ≤
      actualSourceSimilarity (Matrix.diagonal diagonal-weightsᵀ*weights) scale row row)
    (bias : N → ℝ) (first second : M → ℝ) :
    ∀ activation ∈ ({(fun value : ℝ => max value 0),Real.tanh,Real.sigmoid} : Set (ℝ → ℝ)),
      ‖WithLp.toLp 2 (actualSLL weights diagonal activation bias first-
        actualSLL weights diagonal activation bias second)‖ ≤ ‖WithLp.toLp 2 (first-second)‖ := by
  intro activation hactivation
  exact actual_sll_is_euclidean_nonexpansive weights diagonal
    (actual_positive_similarity_centers_force_positive_diagonal weights diagonal scale hscale hcenters)
    (actual_source_scaled_diagonal_dominance_implies_gram_certificate weights diagonal scale hscale hdominant)
    activation (actual_standard_activations_have_unit_interval_chords activation hactivation) bias first second

end SafeLearning.CompleteModulesSLLCorollaries
