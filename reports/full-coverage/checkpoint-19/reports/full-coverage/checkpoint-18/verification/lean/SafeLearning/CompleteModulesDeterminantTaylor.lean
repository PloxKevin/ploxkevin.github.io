import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial Filter Asymptotics
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesDeterminantTaylor

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualDeterminantRemainder (direction : Matrix N N ℝ) : Polynomial ℝ :=
  (Matrix.det (1+(Polynomial.X : Polynomial ℝ) • direction.map Polynomial.C)).divX.divX

theorem actual_determinant_exact_second_order_expansion
    (direction : Matrix N N ℝ) (step : ℝ) :
    (1+step • direction).det=1+step*direction.trace+
      (actualDeterminantRemainder direction).eval step*step^2 := by
  simpa only [actualDeterminantRemainder,mul_comm step direction.trace]
    using Matrix.det_one_add_smul step direction

theorem actual_determinant_second_order_remainder_is_bigO (direction : Matrix N N ℝ) :
    (fun step : ℝ => (1+step • direction).det-1-step*direction.trace) =O[𝓝 0]
      (fun step : ℝ => step^2) := by
  have hbound : (fun step : ℝ => (actualDeterminantRemainder direction).eval step) =O[𝓝 0]
      (fun _ : ℝ => (1:ℝ)) :=
    (actualDeterminantRemainder direction).continuous.continuousAt.isBigO
  have hproduct := hbound.mul (isBigO_refl (fun step : ℝ => step^2) (𝓝 0))
  have he : (fun step : ℝ => (1+step • direction).det-1-step*direction.trace)=
      (fun step : ℝ => (actualDeterminantRemainder direction).eval step*step^2) := by
    funext step
    rw [actual_determinant_exact_second_order_expansion]
    ring
  rw [he]
  simpa only [one_mul] using hproduct

theorem actual_determinant_perturbation_factorization
    (matrix direction : Matrix N N ℝ) (hnonsingular : matrix.det ≠ 0) (step : ℝ) :
    (matrix+step • direction).det=matrix.det*(1+step • (matrix⁻¹*direction)).det := by
  have he : matrix+step • direction=matrix*(1+step • (matrix⁻¹*direction)) := by
    rw [Matrix.mul_add,Matrix.mul_one,Matrix.mul_smul,← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv matrix (isUnit_iff_ne_zero.mpr hnonsingular),Matrix.one_mul]
  rw [he,Matrix.det_mul]

theorem actual_general_determinant_second_order_expansion
    (matrix direction : Matrix N N ℝ) (hnonsingular : matrix.det ≠ 0) :
    (fun step : ℝ => (matrix+step • direction).det-matrix.det-
      step*(matrix.det*(matrix⁻¹*direction).trace)) =O[𝓝 0] (fun step : ℝ => step^2) := by
  have h := (actual_determinant_second_order_remainder_is_bigO (matrix⁻¹*direction)).const_mul_left matrix.det
  have he : (fun step : ℝ => (matrix+step • direction).det-matrix.det-
      step*(matrix.det*(matrix⁻¹*direction).trace))=
      (fun step : ℝ => matrix.det*((1+step • (matrix⁻¹*direction)).det-1-
        step*(matrix⁻¹*direction).trace)) := by
    funext step
    rw [actual_determinant_perturbation_factorization matrix direction hnonsingular]
    ring
  rw [he]
  exact h

end SafeLearning.CompleteModulesDeterminantTaylor
