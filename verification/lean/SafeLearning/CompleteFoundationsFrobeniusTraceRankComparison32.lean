import SafeLearning.CompleteFoundationsInducedNormProductCertificates30
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
namespace SafeLearning.CompleteFoundationsFrobeniusTraceRankComparison32
open CompleteFoundationsInducedNormProductCertificates30
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def literalFrobenius (A : Matrix m n ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2)

section FrobeniusNorm
open scoped Matrix.Norms.Frobenius

theorem actual_literal_frobenius_is_the_matrix_frobenius_norm (A : Matrix m n ℝ) :
    literalFrobenius A = ‖A‖ := by
  unfold literalFrobenius
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem actual_matrix_times_a_column_is_the_actual_matrix_vector_product
    (A : Matrix m n ℝ) (x : n → ℝ) :
    A * Matrix.replicateCol Unit x = Matrix.replicateCol Unit (A *ᵥ x) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.mulVec, dotProduct]

theorem actual_rectangular_euclidean_matrix_action_is_bounded_by_frobenius
    (A : Matrix m n ℝ) (x : PiLp 2 (fun _ : n => ℝ)) :
    ‖sourceMatrixMap 2 2 A x‖ ≤ literalFrobenius A * ‖x‖ := by
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit (WithLp.ofLp x))
  rw [actual_matrix_times_a_column_is_the_actual_matrix_vector_product,
    Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol,
    ← actual_literal_frobenius_is_the_matrix_frobenius_norm] at h
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ literalFrobenius A * ‖x‖
  simpa only [WithLp.toLp_ofLp] using h

end FrobeniusNorm

theorem actual_trace_inner_product_is_the_full_entrywise_inner_product
    (A B : Matrix m n ℝ) : Matrix.trace (Aᵀ * B) = ∑ i, ∑ j, A i j * B i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem actual_frobenius_is_the_square_root_of_the_actual_gram_trace
    (A : Matrix m n ℝ) : literalFrobenius A = Real.sqrt (Matrix.trace (Aᵀ * A)) := by
  rw [actual_trace_inner_product_is_the_full_entrywise_inner_product]
  simp only [literalFrobenius, pow_two]

theorem actual_frobenius_is_the_euclidean_norm_of_one_flattened_vector
    (A : Matrix m n ℝ) :
    literalFrobenius A = ‖WithLp.toLp 2 (fun ij : m × n => A ij.1 ij.2)‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type, literalFrobenius]

theorem actual_euclidean_operator_norm_is_bounded_by_frobenius
    (A : Matrix m n ℝ) : ‖sourceMatrixMap 2 2 A‖ ≤ literalFrobenius A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact actual_rectangular_euclidean_matrix_action_is_bounded_by_frobenius A

private theorem actual_gram_is_hermitian (A : Matrix m n ℝ) :
    (Aᵀ * A).IsHermitian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self A

theorem actual_gram_eigenvalue_is_the_squared_norm_of_a_true_unit_eigenvector_image
    (A : Matrix m n ℝ) (i : n) :
    (actual_gram_is_hermitian A).eigenvalues i =
      ‖sourceMatrixMap 2 2 A ((actual_gram_is_hermitian A).eigenvectorBasis i)‖ ^ 2 := by
  rw [(actual_gram_is_hermitian A).eigenvalues_eq]
  simp only [RCLike.re_to_real, star_trivial]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [sourceMatrixMap, RCLike.inner_apply, conj_trivial, dotProduct, pow_two]

theorem actual_each_gram_eigenvalue_is_nonnegative_and_bounded_by_operator_norm_squared
    (A : Matrix m n ℝ) (i : n) :
    0 ≤ (actual_gram_is_hermitian A).eigenvalues i ∧
      (actual_gram_is_hermitian A).eigenvalues i ≤ ‖sourceMatrixMap 2 2 A‖ ^ 2 := by
  rw [actual_gram_eigenvalue_is_the_squared_norm_of_a_true_unit_eigenvector_image]
  have h := (sourceMatrixMap 2 2 A).le_opNorm ((actual_gram_is_hermitian A).eigenvectorBasis i)
  rw [(actual_gram_is_hermitian A).eigenvectorBasis.orthonormal.norm_eq_one i, mul_one] at h
  refine ⟨sq_nonneg _, ?_⟩
  have hnormA : 0 ≤ ‖sourceMatrixMap 2 2 A‖ := norm_nonneg _
  have hnormImage : 0 ≤ ‖sourceMatrixMap 2 2 A ((actual_gram_is_hermitian A).eigenvectorBasis i)‖ := norm_nonneg _
  nlinarith

theorem actual_gram_trace_has_the_sharp_rank_times_operator_norm_squared_bound
    (A : Matrix m n ℝ) :
    Matrix.trace (Aᵀ * A) ≤ (Matrix.rank A : ℝ) * ‖sourceMatrixMap 2 2 A‖ ^ 2 := by
  classical
  let h := actual_gram_is_hermitian A
  let S := Finset.univ.filter (fun i : n => h.eigenvalues i ≠ 0)
  have hsum : (∑ i, h.eigenvalues i) = ∑ i ∈ S, h.eigenvalues i := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : h.eigenvalues i = 0 := by simpa [S] using hi
    exact hz
  have hcard : S.card = Matrix.rank A := by
    have hr := h.rank_eq_card_non_zero_eigs
    rw [Matrix.rank_transpose_mul_self] at hr
    simpa [S, Fintype.card_subtype] using hr.symm
  rw [h.trace_eq_sum_eigenvalues]
  change (∑ i, h.eigenvalues i) ≤ (Matrix.rank A : ℝ) * ‖sourceMatrixMap 2 2 A‖ ^ 2
  rw [hsum]
  calc
    (∑ i ∈ S, h.eigenvalues i) ≤ ∑ i ∈ S, ‖sourceMatrixMap 2 2 A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (actual_each_gram_eigenvalue_is_nonnegative_and_bounded_by_operator_norm_squared A i).2
    _ = (Matrix.rank A : ℝ) * ‖sourceMatrixMap 2 2 A‖ ^ 2 := by
      simp [hcard]

theorem actual_rectangular_frobenius_has_the_sharp_two_sided_rank_comparison
    (A : Matrix m n ℝ) :
    ‖sourceMatrixMap 2 2 A‖ ≤ literalFrobenius A ∧
      literalFrobenius A ≤ Real.sqrt (Matrix.rank A) * ‖sourceMatrixMap 2 2 A‖ := by
  refine ⟨actual_euclidean_operator_norm_is_bounded_by_frobenius A, ?_⟩
  rw [actual_frobenius_is_the_square_root_of_the_actual_gram_trace]
  calc
    Real.sqrt (Matrix.trace (Aᵀ * A)) ≤
        Real.sqrt ((Matrix.rank A : ℝ) * ‖sourceMatrixMap 2 2 A‖ ^ 2) :=
      Real.sqrt_le_sqrt (actual_gram_trace_has_the_sharp_rank_times_operator_norm_squared_bound A)
    _ = Real.sqrt (Matrix.rank A) * ‖sourceMatrixMap 2 2 A‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem actual_frobenius_identity_is_square_root_dimension :
    literalFrobenius (1 : Matrix n n ℝ) = Real.sqrt (Fintype.card n) := by
  simp [literalFrobenius, Matrix.one_apply]

theorem actual_two_dimensional_identity_separates_frobenius_from_every_induced_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ‖ContinuousLinearMap.id ℝ E‖ = 1 ∧
      1 < literalFrobenius (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨ContinuousLinearMap.norm_id, ?_⟩
  rw [actual_frobenius_identity_is_square_root_dimension]
  norm_num only [Fintype.card_fin]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

theorem actual_printed_running_matrix_has_exact_frobenius_and_the_true_rounding :
    literalFrobenius (!![(2 : ℝ), 2; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) = Real.sqrt 10 ∧
      |Real.sqrt 10 - (3.16 : ℝ)| < 0.005 := by
  refine ⟨by norm_num [literalFrobenius, Fin.sum_univ_two], ?_⟩
  apply abs_lt.mpr
  constructor <;> nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

end SafeLearning.CompleteFoundationsFrobeniusTraceRankComparison32

namespace SafeLearning.CompleteFoundationsFrobeniusTraceRankComparison32
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem actual_trace_pairing_is_the_true_euclidean_inner_product_of_flattened_matrices
    (A B : Matrix m n ℝ) :
    Matrix.trace (Aᵀ * B) =
      ⟪WithLp.toLp 2 (fun ij : m × n => A ij.1 ij.2),
        WithLp.toLp 2 (fun ij : m × n => B ij.1 ij.2)⟫ := by
  rw [actual_trace_inner_product_is_the_full_entrywise_inner_product, PiLp.inner_apply]
  simp [Fintype.sum_prod_type, RCLike.inner_apply, conj_trivial, mul_comm]

end SafeLearning.CompleteFoundationsFrobeniusTraceRankComparison32
