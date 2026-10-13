import SafeLearning.CompleteModulesDiagonalQCChordBridge35

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators

namespace SafeLearning.CompleteModulesDiagonalMultiplierBasis35

variable {K : Type*} [Fintype K] [DecidableEq K]

def coordinateVector (k : K) : K → ℝ := Pi.single k 1

theorem weighted_coordinate_outer_products_are_the_diagonal_matrix (weight : K → ℝ) :
    (∑ k, weight k • Matrix.vecMulVec (coordinateVector k) (coordinateVector k)) =
      Matrix.diagonal weight := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sum_apply, Matrix.vecMulVec, coordinateVector, Pi.single_apply]
  · simp [Matrix.sum_apply, Matrix.vecMulVec, coordinateVector, Pi.single_apply, hij]

omit [Fintype K] in
theorem nonnegative_weights_are_exactly_positive_semidefinite_diagonal_matrices
    (weight : K → ℝ) :
    (Matrix.diagonal weight).PosSemidef ↔ ∀ k, 0 ≤ weight k := by
  exact Matrix.posSemidef_diagonal_iff

theorem printed_multiplier_sum_is_positive_semidefinite
    (weight : K → ℝ) (hweight : ∀ k, 0 ≤ weight k) :
    (∑ k, weight k • Matrix.vecMulVec (coordinateVector k) (coordinateVector k)).PosSemidef := by
  rw [weighted_coordinate_outer_products_are_the_diagonal_matrix]
  exact nonnegative_weights_are_exactly_positive_semidefinite_diagonal_matrices weight |>.mpr hweight

end SafeLearning.CompleteModulesDiagonalMultiplierBasis35
