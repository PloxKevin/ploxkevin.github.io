import SafeLearning.CompleteFoundationsMatrixConjugate
import SafeLearning.CompleteFoundationsShiftedConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteFoundationsConjugateConsequences

open Set
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem actual_euclidean_pairing_objective_correspondence
    (Q : Matrix n n ℝ) (y x : EuclideanSpace ℝ n) :
    CompleteFoundationsMatrixConjugate.euclideanPairingObjective Q y x =
      CompleteFoundationsMatrixConjugate.pairingObjective Q
        (y : n → ℝ) (x : n → ℝ) := by
  rw [CompleteFoundationsMatrixConjugate.euclideanPairingObjective,
    CompleteFoundationsMatrixConjugate.actual_euclidean_quadratic_correspondence]
  simp only [CompleteFoundationsMatrixConjugate.pairingObjective,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct, mul_comm]

theorem actual_matrix_inverse_optimizer_has_zero_gradient
    (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y : EuclideanSpace ℝ n) :
    HasGradientAt (CompleteFoundationsMatrixConjugate.euclideanPairingObjective Q y)
      0 (WithLp.toLp 2 (CompleteFoundationsMatrixConjugate.optimizer Q (y : n → ℝ))) := by
  have hi := CompleteFoundationsMatrixConjugate.actual_inverse_stationary_solution
    Q hQ (y : n → ℝ)
  have hop : CompleteFoundationsMatrixConjugate.operator Q
      (WithLp.toLp 2 (CompleteFoundationsMatrixConjugate.optimizer Q (y : n → ℝ))) = y := by
    ext i
    exact congrFun hi i
  simpa only [hop, sub_self] using
    CompleteFoundationsMatrixConjugate.actual_pairing_objective_gradient Q hQ.isHermitian y
      (WithLp.toLp 2 (CompleteFoundationsMatrixConjugate.optimizer Q (y : n → ℝ)))

def smoothShiftedFunction (w : ℝ) : ℝ := (w - 1) ^ 2 / 2

theorem actual_shifted_function_has_derivative (w : ℝ) :
    HasDerivAt smoothShiftedFunction (w - 1) w := by
  convert (((hasDerivAt_id w).sub_const 1).pow 2).div_const 2 using 1
  · rfl
  · simp only [id_eq]
    ring

theorem actual_shifted_restricted_function_interior_correspondence (w : ℝ) (hw : 0 < w) :
    CompleteFoundationsShiftedConjugate.sourceFunction w = (smoothShiftedFunction w : EReal) ∧
    HasDerivWithinAt smoothShiftedFunction (w - 1) (Ioi 0) w := by
  refine ⟨?_, (actual_shifted_function_has_derivative w).hasDerivWithinAt⟩
  simp only [CompleteFoundationsShiftedConjugate.sourceFunction,
    if_pos (le_of_lt hw), smoothShiftedFunction]

theorem actual_shifted_function_derivative_at_two :
    HasDerivAt smoothShiftedFunction 1 2 ∧
    CompleteFoundationsShiftedConjugate.sourceFunction 2 = (smoothShiftedFunction 2 : EReal) := by
  constructor
  · convert actual_shifted_function_has_derivative 2 using 1 <;> norm_num
  · exact (actual_shifted_restricted_function_interior_correspondence 2 (by norm_num)).1

end SafeLearning.CompleteFoundationsConjugateConsequences
