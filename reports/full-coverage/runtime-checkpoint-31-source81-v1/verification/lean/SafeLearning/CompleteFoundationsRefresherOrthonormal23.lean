import SafeLearning.CompleteFoundationsSpectralModels
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsRefresherOrthonormal23
open SafeLearning.CompleteFoundationsSpectralModels

theorem actual_printed_unnormalized_directions_are_perpendicular :
    inner ℝ (point 1 1) (point 1 (-1))=0 := by
  rw [inner_coordinate_formula]
  norm_num [point]

theorem actual_both_printed_direction_lengths_are_sqrt_two :
    ‖point 1 1‖=Real.sqrt 2 ∧ ‖point 1 (-1)‖=Real.sqrt 2 := by
  have hp : ‖point 1 1‖^2=2 := by rw [norm_squared_coordinates];norm_num [point]
  have hm : ‖point 1 (-1)‖^2=2 := by rw [norm_squared_coordinates];norm_num [point]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [norm_nonneg (point 1 1),norm_nonneg (point 1 (-1)),Real.sqrt_nonneg 2]

theorem actual_division_by_sqrt_two_is_the_printed_normalization :
    (Real.sqrt 2)⁻¹ • point 1 1=qPlus ∧
      (Real.sqrt 2)⁻¹ • point 1 (-1)=qMinus := by
  constructor <;> ext i <;> fin_cases i <;> simp [point,qPlus,qMinus] <;> ring

theorem actual_printed_normalized_directions_are_orthonormal :
    Orthonormal ℝ (![qPlus,qMinus] : Fin 2 → E) := source_orthonormal

theorem actual_two_normalized_directions_are_a_complete_spanning_family (x : E) :
    x=inner ℝ qPlus x • qPlus+inner ℝ qMinus x • qMinus := source_eigenbasis_spans x

theorem actual_every_real_symmetric_matrix_has_a_complete_orthonormal_eigenbasis
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsSymm) :
    ∃ (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (eigenvalues : n → ℝ),
      (∀ j,A.mulVec (b j : n → ℝ)=eigenvalues j • (b j : n → ℝ)) ∧
      (∀ x : EuclideanSpace ℝ n,∑ j,inner ℝ (b j) x • b j=x) := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  refine ⟨hH.eigenvectorBasis,hH.eigenvalues,?_,?_⟩
  · exact hH.mulVec_eigenvectorBasis
  · exact hH.eigenvectorBasis.sum_repr'

end SafeLearning.CompleteFoundationsRefresherOrthonormal23
