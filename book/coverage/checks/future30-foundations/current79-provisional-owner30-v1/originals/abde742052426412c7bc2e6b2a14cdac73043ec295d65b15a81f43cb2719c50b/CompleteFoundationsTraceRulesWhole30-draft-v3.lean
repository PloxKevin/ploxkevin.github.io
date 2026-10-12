import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace SafeLearning.CompleteFoundationsTraceRulesWhole30

variable {M N P : Type*} [Fintype M] [Fintype N] [Fintype P]
variable [DecidableEq M] [DecidableEq N] [DecidableEq P]

theorem actual_trace_is_the_sum_of_actual_diagonal_entries (A : Matrix N N ℝ) :
    A.trace = ∑ i, A i i := rfl

theorem actual_arbitrary_complex_trace_is_the_sum_of_all_eigenvalues_with_multiplicity
    (A : Matrix N N ℂ) : A.trace = A.charpoly.roots.sum :=
  Matrix.trace_eq_sum_roots_charpoly A

theorem actual_arbitrary_real_trace_is_the_sum_of_complex_eigenvalues_with_multiplicity
    (A : Matrix N N ℝ) :
    (A.trace : ℂ) = (A.map Complex.ofReal).charpoly.roots.sum := by
  rw [← actual_arbitrary_complex_trace_is_the_sum_of_all_eigenvalues_with_multiplicity]
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply]

theorem actual_rectangular_two_factor_trace_is_the_coordinate_pairing_and_commutes
    (A : Matrix M N ℝ) (B : Matrix N M ℝ) :
    (A*B).trace = ∑ i, ∑ j, A i j*B j i ∧ (A*B).trace = (B*A).trace := by
  exact ⟨rfl,Matrix.trace_mul_comm A B⟩

theorem actual_compatible_three_factor_trace_is_cyclic
    (A : Matrix M N ℝ) (B : Matrix N P ℝ) (C : Matrix P M ℝ) :
    (A*B*C).trace = (C*A*B).trace := Matrix.trace_mul_cycle A B C

theorem actual_other_trace_reordering_can_change_the_value :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;1,0]
    (A*B*C).trace = 1 ∧ (A*C*B).trace = 0 := by
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

theorem actual_trace_is_preserved_under_true_invertible_similarity
    (A S : Matrix N N ℝ) (hS : S.det ≠ 0) :
    (S⁻¹*A*S).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS),Matrix.one_mul]

theorem actual_quadratic_form_is_the_trace_of_the_actual_outer_product_lift
    (A : Matrix N N ℝ) (x : N → ℝ) :
    x ⬝ᵥ A.mulVec x = (A*Matrix.vecMulVec x x).trace := by
  rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

theorem actual_PSD_square_root_is_a_genuine_unique_PSD_matrix_square_root
    (A : Matrix N N ℝ) (hA : A.PosSemidef) :
    (CFC.sqrt A).PosSemidef ∧ CFC.sqrt A*CFC.sqrt A=A ∧
      ∀ R : Matrix N N ℝ, R.PosSemidef → R*R=A → R=CFC.sqrt A := by
  refine ⟨(CFC.sqrt_nonneg A).posSemidef,CFC.sqrt_mul_sqrt_self A hA.nonneg,?_⟩
  intro R hR hsquare
  exact (CFC.sqrt_unique hsquare hR.nonneg).symm

theorem actual_PSD_trace_pairing_has_the_printed_square_root_route_and_is_nonnegative
    (A B : Matrix N N ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A*B).trace=(CFC.sqrt A*B*CFC.sqrt A).trace ∧ 0 ≤ (A*B).trace := by
  let R : Matrix N N ℝ := CFC.sqrt A
  have hroot := actual_PSD_square_root_is_a_genuine_unique_PSD_matrix_square_root A hA
  have hr : R*R=A := hroot.2.1
  have hcyclic : (A*B).trace=(R*B*R).trace := by
    rw [← hr]
    exact (Matrix.trace_mul_cycle R B R).symm
  have hsym : Rᵀ=R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hroot.1.isHermitian.eq
  have hpsd : (R*B*R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,hsym] using hB.conjTranspose_mul_mul_same R
  refine ⟨hcyclic,?_⟩
  rw [hcyclic]
  exact hpsd.trace_nonneg

end SafeLearning.CompleteFoundationsTraceRulesWhole30
