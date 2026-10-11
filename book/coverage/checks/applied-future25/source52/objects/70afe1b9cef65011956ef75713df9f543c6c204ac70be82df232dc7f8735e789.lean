import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesMatrixError

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualQuadratic (matrix : Matrix N N ℝ) (vector : N → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

theorem actual_quadratic_error_is_bounded_by_spectral_norm
    (error : Matrix N N ℝ) (vector : N → ℝ) :
    |actualQuadratic error vector| ≤ ‖error‖*‖WithLp.toLp 2 vector‖^2 := by
  have hinner : inner ℝ (WithLp.toLp 2 vector) (WithLp.toLp 2 (error *ᵥ vector))=
      actualQuadratic error vector := by
    simp [EuclideanSpace.inner_toLp_toLp,actualQuadratic,dotProduct,mul_comm]
  have hcauchy := abs_real_inner_le_norm (WithLp.toLp 2 vector)
    (WithLp.toLp 2 (error *ᵥ vector))
  have hgain := Matrix.l2_opNorm_mulVec error (WithLp.toLp 2 vector)
  rw [hinner] at hcauchy
  calc
    _ ≤ ‖WithLp.toLp 2 vector‖*‖WithLp.toLp 2 (error *ᵥ vector)‖ := hcauchy
    _ ≤ ‖WithLp.toLp 2 vector‖*(‖error‖*‖WithLp.toLp 2 vector‖) :=
      mul_le_mul_of_nonneg_left hgain (norm_nonneg _)
    _ = _ := by ring

theorem actual_quadratic_shift (matrix : Matrix N N ℝ) (margin : ℝ) (vector : N → ℝ) :
    actualQuadratic (matrix-margin • 1) vector=
      actualQuadratic matrix vector-margin*‖WithLp.toLp 2 vector‖^2 := by
  have hnorm : ‖WithLp.toLp 2 vector‖^2=∑ i, vector i^2 := by
    simpa [Real.norm_eq_abs,sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : N => ℝ) (WithLp.toLp 2 vector)
  simp [actualQuadratic,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct,hnorm,
    Finset.sum_sub_distrib,Finset.mul_sum,pow_two,mul_sub,mul_assoc,mul_comm,mul_left_comm]

theorem actual_validated_matrix_margin_certifies_positive_definiteness
    (actual computed : Matrix N N ℝ) (margin : ℝ) (hsymmetric : actual.IsHermitian)
    (herror : ‖actual-computed‖ ≤ margin) (hmargin : (computed-margin • 1).PosDef) :
    actual.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsymmetric
  intro vector hvector
  have hpositive := hmargin.dotProduct_mulVec_pos hvector
  change 0 < actualQuadratic (computed-margin • 1) vector at hpositive
  rw [actual_quadratic_shift] at hpositive
  have herrorquadratic := actual_quadratic_error_is_bounded_by_spectral_norm (actual-computed) vector
  have herrorbound : |actualQuadratic (actual-computed) vector| ≤ margin*‖WithLp.toLp 2 vector‖^2 :=
    herrorquadratic.trans (mul_le_mul_of_nonneg_right herror (sq_nonneg _))
  have hquadratic : actualQuadratic (actual-computed) vector=
      actualQuadratic actual vector-actualQuadratic computed vector := by
    simp [actualQuadratic,Matrix.sub_mulVec,dotProduct,Finset.sum_sub_distrib,mul_sub]
  rw [hquadratic] at herrorbound
  have hlower := (abs_le.mp herrorbound).1
  simpa [actualQuadratic] using (show 0 < actualQuadratic actual vector by linarith)

def positiveNearSingular (epsilon : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal (fun _ => epsilon/4)

def indefiniteNearSingular (epsilon : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal (fun _ => -epsilon/4)

theorem actual_near_singular_matrix_is_positive (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (positiveNearSingular epsilon).PosDef := by
  rw [positiveNearSingular,Matrix.posDef_diagonal_iff]
  intro i
  linarith

theorem actual_near_singular_matrix_is_not_positive (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ¬(indefiniteNearSingular epsilon).PosDef := by
  intro hpositive
  have h := hpositive.diag_pos (i := (0 : Fin 1))
  simp [indefiniteNearSingular] at h
  linarith

theorem actual_opposite_feasibility_matrices_are_arbitrarily_close
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ‖positiveNearSingular epsilon-indefiniteNearSingular epsilon‖ < epsilon := by
  have he : positiveNearSingular epsilon-indefiniteNearSingular epsilon=
      Matrix.diagonal (fun _ : Fin 1 => epsilon/2) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [positiveNearSingular,indefiniteNearSingular]
    ring
  rw [he,Matrix.l2_opNorm_diagonal]
  simp only [Pi.norm_def,Real.norm_eq_abs]
  norm_num [abs_of_pos (show 0 < epsilon/2 by linarith),abs_of_pos hepsilon]
  linarith

theorem actual_small_absolute_error_can_reverse_both_feasibility_decisions
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ positive negative : Matrix (Fin 1) (Fin 1) ℝ,
      positive.PosDef ∧ ¬negative.PosDef ∧
        ‖positive-negative‖ < epsilon ∧ ‖negative-positive‖ < epsilon := by
  refine ⟨positiveNearSingular epsilon,indefiniteNearSingular epsilon,
    actual_near_singular_matrix_is_positive epsilon hepsilon,
    actual_near_singular_matrix_is_not_positive epsilon hepsilon,
    actual_opposite_feasibility_matrices_are_arbitrarily_close epsilon hepsilon,?_⟩
  rw [norm_sub_rev]
  exact actual_opposite_feasibility_matrices_are_arbitrarily_close epsilon hepsilon

end SafeLearning.CompleteModulesMatrixError
