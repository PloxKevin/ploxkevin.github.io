import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesComplexBasics

theorem actual_imaginary_unit_squared : Complex.I^2= -1 := Complex.I_sq

theorem actual_complex_conjugate_coordinates (realPart imaginaryPart : ℝ) :
    star ((realPart:ℂ)+(imaginaryPart:ℂ)*Complex.I)=
      (realPart:ℂ)-(imaginaryPart:ℂ)*Complex.I := by
  simp
  ring

theorem actual_complex_modulus_squared_coordinates (realPart imaginaryPart : ℝ) :
    ‖(realPart:ℂ)+(imaginaryPart:ℂ)*Complex.I‖^2=realPart^2+imaginaryPart^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,pow_two]

theorem actual_complex_modulus_squared_is_conjugate_product (value : ℂ) :
    ((‖value‖^2:ℝ):ℂ)=star value*value := by
  simpa using (Complex.conj_mul' value).symm

theorem actual_matrix_adjoint_entries
    {N M : Type*} (matrix : Matrix N M ℂ) (row : M) (column : N) :
    matrixᴴ row column=star (matrix column row) := rfl

theorem actual_matrix_hermitian_definition
    {N : Type*} (matrix : Matrix N N ℂ) :
    matrix.IsHermitian ↔ matrixᴴ=matrix := Iff.rfl

theorem actual_matrix_unitarity_definition
    {N : Type*} [Fintype N] [DecidableEq N] (matrix : Matrix N N ℂ) :
    matrix ∈ Matrix.unitaryGroup N ℂ ↔ matrixᴴ*matrix=1 :=
  Matrix.mem_unitaryGroup_iff'

theorem actual_complex_vector_squared_norm_is_adjoint_product
    {N : Type*} [Fintype N] (vector : N → ℂ) :
    ((‖WithLp.toLp 2 vector‖^2:ℝ):ℂ)=star vector ⬝ᵥvector := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : N => ℂ)]
  simp only [Complex.ofReal_sum,dotProduct,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro coordinate hcoordinate
  exact actual_complex_modulus_squared_is_conjugate_product (vector coordinate)

def actualImaginaryMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of (fun _ _ => Complex.I)

theorem actual_imaginary_matrix_is_skew_hermitian :
    actualImaginaryMatrixᴴ= -actualImaginaryMatrix := by
  ext row column
  fin_cases row
  fin_cases column
  simp [actualImaginaryMatrix]

theorem actual_imaginary_matrix_is_unitary :
    actualImaginaryMatrixᴴ*actualImaginaryMatrix=1 := by
  ext row column
  fin_cases row
  fin_cases column
  simp [actualImaginaryMatrix,Matrix.mul_apply]

end SafeLearning.CompleteModulesComplexBasics
