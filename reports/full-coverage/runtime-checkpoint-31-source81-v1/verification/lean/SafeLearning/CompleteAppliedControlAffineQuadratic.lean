import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedControlAffineQuadratic

variable {n m constraints : Type*} [Fintype n] [Fintype m] [Fintype constraints] [DecidableEq m]

def derivativeOffset (gradient drift : n→ℝ) : ℝ := gradient⬝ᵥdrift
def derivativeInputRow (gradient : n→ℝ) (inputMatrix : Matrix n m ℝ) : m→ℝ :=
  Matrix.vecMul gradient inputMatrix

theorem actual_control_affine_lie_derivative_has_the_literal_linear_input_row
    (gradient drift : n→ℝ) (inputMatrix : Matrix n m ℝ) (input : m→ℝ) :
    gradient⬝ᵥ(drift+inputMatrix.mulVec input)=
      derivativeOffset gradient drift+derivativeInputRow gradient inputMatrix⬝ᵥinput := by
  rw [dotProduct_add,Matrix.dotProduct_mulVec]
  rfl

theorem actual_all_derivative_constraints_have_the_literal_matrix_inequality_form
    (gradient : constraints→n→ℝ) (drift : n→ℝ)
    (inputMatrix : Matrix n m ℝ) (threshold : constraints→ℝ) (input : m→ℝ) :
    (∀i,threshold i≤gradient i⬝ᵥ(drift+inputMatrix.mulVec input)) ↔
      ∀i,Matrix.mulVec ((fun i j=> -derivativeInputRow (gradient i) inputMatrix j):Matrix constraints m ℝ) input i≤
        derivativeOffset (gradient i) drift-threshold i := by
  constructor <;> intro h i
  · have hi := h i
    rw [actual_control_affine_lie_derivative_has_the_literal_linear_input_row] at hi
    simp only [Matrix.mulVec,dotProduct,neg_mul,Finset.sum_neg_distrib]
    change -(derivativeInputRow (gradient i) inputMatrix⬝ᵥinput)≤
      derivativeOffset (gradient i) drift-threshold i
    linarith
  · have hi := h i
    simp only [Matrix.mulVec,dotProduct,neg_mul,Finset.sum_neg_distrib] at hi
    change -(derivativeInputRow (gradient i) inputMatrix⬝ᵥinput)≤
      derivativeOffset (gradient i) drift-threshold i at hi
    rw [actual_control_affine_lie_derivative_has_the_literal_linear_input_row]
    linarith

def actualClosestInputCost (desired input : EuclideanSpace ℝ m) : ℝ := ‖input-desired‖^2

theorem actual_closest_input_squared_distance_is_a_quadratic_polynomial
    (desired input : EuclideanSpace ℝ m) :
    actualClosestInputCost desired input=
      (∑i,input i^2)-2*(∑i,desired i*input i)+(∑i,desired i^2) := by
  rw [actualClosestInputCost,EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply]
  calc
    (∑i,(input i-desired i)^2)=∑i,(input i^2-2*(desired i*input i)+desired i^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]

theorem actual_minimizing_that_quadratic_is_exactly_choosing_a_closest_input
    (allowed : Set (EuclideanSpace ℝ m)) (desired candidate : EuclideanSpace ℝ m) :
    (candidate∈allowed ∧ ∀input∈allowed,
      actualClosestInputCost desired candidate≤actualClosestInputCost desired input) ↔
      candidate∈allowed ∧ ∀input∈allowed,‖candidate-desired‖≤‖input-desired‖ := by
  simp only [actualClosestInputCost,sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

theorem actual_closest_input_quadratic_has_the_literal_identity_matrix_coefficients
    (desired input : EuclideanSpace ℝ m) :
    actualClosestInputCost desired input=
      (fun i=>input i)⬝ᵥ((1:Matrix m m ℝ).mulVec (fun i=>input i))+
        (fun i=> -2*desired i)⬝ᵥ(fun i=>input i)+(∑i,desired i^2) := by
  rw [actual_closest_input_squared_distance_is_a_quadratic_polynomial,Matrix.one_mulVec]
  have hquad : (fun i=>input i)⬝ᵥ(fun i=>input i)=∑i,input i^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlinear : (fun i=> -2*desired i)⬝ᵥ(fun i=>input i)= -2*(∑i,desired i*input i) := by
    simp only [dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hquad,hlinear]
  ring

end SafeLearning.CompleteAppliedControlAffineQuadratic
