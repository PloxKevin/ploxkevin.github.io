import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set
open scoped BigOperators MatrixOrder

namespace SafeLearning.CompleteFoundationsSymmetricFunctionalCalculus30
variable {n : Type*} [Fintype n] [DecidableEq n]

def actualFunction (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => f (hA.eigenvalues i)))

theorem actual_function_is_the_true_orthogonal_diagonal_conjugation
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    actualFunction A hA f = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ).transpose := by
  simp only [actualFunction, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem actual_function_is_the_sum_of_eigenvector_rank_one_matrices
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    actualFunction A hA f = ∑ j, f (hA.eigenvalues j) •
      Matrix.vecMulVec (hA.eigenvectorBasis j : n → ℝ) (hA.eigenvectorBasis j : n → ℝ) := by
  rw [actual_function_is_the_true_orthogonal_diagonal_conjugation]
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorUnitary_apply,hA.eigenvectorUnitary_apply]
  ring

theorem actual_function_agrees_with_finite_spectrum_continuous_functional_calculus
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    actualFunction A hA f = cfc f A := by
  rw [hA.cfc_eq]
  rfl

theorem actual_identity_function_reconstructs_the_original_matrix
    (A : Matrix n n ℝ) (hA : A.IsHermitian) : actualFunction A hA id = A := by
  simpa only [actualFunction, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq] using hA.spectral_theorem.symm

theorem actual_constant_function_is_a_scalar_identity_matrix
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (r : ℝ) :
    actualFunction A hA (fun _ => r) = r • (1 : Matrix n n ℝ) := by
  unfold actualFunction
  have hd : Matrix.diagonal (fun _ : n => r) = r • (1 : Matrix n n ℝ) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  rw [hd, map_smul, map_one]

theorem actual_function_addition_is_matrix_addition
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    actualFunction A hA (fun x => f x + g x) = actualFunction A hA f + actualFunction A hA g := by
  unfold actualFunction
  rw [← map_add, ← Matrix.diagonal_add]

theorem actual_function_multiplication_is_matrix_multiplication
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    actualFunction A hA (fun x => f x * g x) = actualFunction A hA f * actualFunction A hA g := by
  unfold actualFunction
  rw [← map_mul, Matrix.diagonal_mul_diagonal]

theorem actual_functions_of_one_matrix_commute
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    actualFunction A hA f * actualFunction A hA g = actualFunction A hA g * actualFunction A hA f := by
  rw [← actual_function_multiplication_is_matrix_multiplication,
    ← actual_function_multiplication_is_matrix_multiplication]
  congr 1
  funext x
  exact mul_comm _ _

theorem actual_function_has_the_same_true_unit_eigenvectors
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) (i : n) :
    actualFunction A hA f *ᵥ (hA.eigenvectorBasis i : n → ℝ) =
      f (hA.eigenvalues i) • (hA.eigenvectorBasis i : n → ℝ) := by
  unfold actualFunction
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hA.star_eigenvectorUnitary_mulVec]
  rw [Matrix.diagonal_mulVec_single, ← smul_eq_mul, Pi.single_smul',
    Matrix.mulVec_smul, hA.eigenvectorUnitary_mulVec]

theorem actual_power_function_agrees_with_every_natural_matrix_power
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (k : ℕ) :
    actualFunction A hA (fun x => x^k) = A^k := by
  rw [actual_function_agrees_with_finite_spectrum_continuous_functional_calculus]
  exact cfc_pow_id A k hA

theorem actual_polynomial_function_agrees_with_matrix_polynomial_evaluation
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : Polynomial ℝ) :
    actualFunction A hA p.eval = Polynomial.aeval A p := by
  rw [actual_function_agrees_with_finite_spectrum_continuous_functional_calculus]
  exact cfc_polynomial p A hA

theorem actual_reciprocal_function_is_the_true_inverse_on_nonzero_eigenvalues
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (hne : ∀ i, hA.eigenvalues i ≠ 0) :
    A⁻¹ = actualFunction A hA (fun x => x⁻¹) := by
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; rw [← actual_identity_function_reconstructs_the_original_matrix A hA]
  rw [← actual_function_multiplication_is_matrix_multiplication]
  have he : (fun x => x⁻¹ * x) ∘ hA.eigenvalues = fun _ => (1:ℝ) := by
    funext i
    exact inv_mul_cancel₀ (hne i)
  change Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal ((fun x => x⁻¹ * x) ∘ hA.eigenvalues)) = 1
  rw [he]
  simp

theorem actual_shifted_reciprocal_is_the_true_shifted_inverse
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (eta : ℝ)
    (hne : ∀ i, hA.eigenvalues i + eta ≠ 0) :
    (A + eta • (1 : Matrix n n ℝ))⁻¹ = actualFunction A hA (fun x => (x+eta)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; lhs; rw [← actual_identity_function_reconstructs_the_original_matrix A hA]
  rw [← actual_constant_function_is_a_scalar_identity_matrix A hA eta,
    ← actual_function_addition_is_matrix_addition,
    ← actual_function_multiplication_is_matrix_multiplication]
  have he : (fun x => (x+eta)⁻¹ * (x+eta)) ∘ hA.eigenvalues = fun _ => (1:ℝ) := by
    funext i
    exact inv_mul_cancel₀ (hne i)
  change Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal ((fun x => (x+eta)⁻¹ * (x+eta)) ∘ hA.eigenvalues)) = 1
  rw [he]
  simp

theorem actual_function_is_positive_semidefinite_iff_each_eigenvalue_is_nonnegative
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (actualFunction A hA f).PosSemidef ↔ ∀ i, 0 ≤ f (hA.eigenvalues i) := by
  simp only [actualFunction, Unitary.conjStarAlgAut_apply,
    Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff, Matrix.posSemidef_diagonal_iff]

theorem actual_comparison_of_functions_reduces_to_scalar_eigenvalue_comparison
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    (actualFunction A hA g - actualFunction A hA f).PosSemidef ↔
      ∀ i, f (hA.eigenvalues i) ≤ g (hA.eigenvalues i) := by
  have he : actualFunction A hA g - actualFunction A hA f =
      actualFunction A hA (fun x => g x-f x) := by
    unfold actualFunction
    rw [← map_sub, ← Matrix.diagonal_sub]
  rw [he,actual_function_is_positive_semidefinite_iff_each_eigenvalue_is_nonnegative]
  simp only [sub_nonneg]

theorem actual_nonnegative_square_root_squares_to_the_original_matrix
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    (actualFunction A hA.isHermitian Real.sqrt)^2 = A := by
  rw [pow_two, ← actual_function_multiplication_is_matrix_multiplication]
  have he : (fun x => Real.sqrt x * Real.sqrt x) ∘ hA.1.eigenvalues = hA.1.eigenvalues := by
    funext i
    exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  unfold actualFunction
  change Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary
    (Matrix.diagonal ((fun x => Real.sqrt x * Real.sqrt x) ∘ hA.1.eigenvalues)) = A
  rw [he]
  exact actual_identity_function_reconstructs_the_original_matrix A hA.1

theorem actual_square_root_is_the_unique_positive_semidefinite_square_root
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    CFC.sqrt A = actualFunction A hA.isHermitian Real.sqrt := by
  have hp : (actualFunction A hA.isHermitian Real.sqrt).PosSemidef :=
    (actual_function_is_positive_semidefinite_iff_each_eigenvalue_is_nonnegative _ _ _).mpr
      (fun i => Real.sqrt_nonneg _)
  apply (CFC.sqrt_eq_iff A _ hA.nonneg hp.nonneg).mpr
  simpa only [pow_two] using actual_nonnegative_square_root_squares_to_the_original_matrix A hA

theorem actual_regularized_positive_semidefinite_filter_has_the_printed_eigenvalues
    (K : Matrix n n ℝ) (hK : K.PosSemidef) (eta : ℝ) (heta : 0 < eta) (i : n) :
    (K * (K + eta • (1 : Matrix n n ℝ))⁻¹) *ᵥ (hK.1.eigenvectorBasis i : n → ℝ) =
      (hK.1.eigenvalues i / (hK.1.eigenvalues i+eta)) •
        (hK.1.eigenvectorBasis i : n → ℝ) ∧
      hK.1.eigenvalues i / (hK.1.eigenvalues i+eta) ∈ Set.Ico (0:ℝ) 1 := by
  have hd (j : n) : 0 < hK.1.eigenvalues j+eta := add_pos_of_nonneg_of_pos (hK.eigenvalues_nonneg j) heta
  rw [actual_shifted_reciprocal_is_the_true_shifted_inverse K hK.1 eta (fun j => (hd j).ne')]
  constructor
  · have heq : K * actualFunction K hK.1 (fun x => (x+eta)⁻¹) =
        actualFunction K hK.1 (fun x => x/(x+eta)) := by
      calc
        K * actualFunction K hK.1 (fun x => (x+eta)⁻¹) =
            actualFunction K hK.1 id * actualFunction K hK.1 (fun x => (x+eta)⁻¹) :=
          congrArg (fun M => M * actualFunction K hK.1 (fun x => (x+eta)⁻¹))
            (actual_identity_function_reconstructs_the_original_matrix K hK.1).symm
        _ = actualFunction K hK.1 (fun x => x/(x+eta)) := by
          rw [← actual_function_multiplication_is_matrix_multiplication]
          congr 1
    rw [heq]
    exact actual_function_has_the_same_true_unit_eigenvectors K hK.1 (fun x => x/(x+eta)) i
  · exact ⟨div_nonneg (hK.eigenvalues_nonneg i) (hd i).le,
      (div_lt_one (hd i)).mpr (lt_add_of_pos_right _ heta)⟩

end SafeLearning.CompleteFoundationsSymmetricFunctionalCalculus30
