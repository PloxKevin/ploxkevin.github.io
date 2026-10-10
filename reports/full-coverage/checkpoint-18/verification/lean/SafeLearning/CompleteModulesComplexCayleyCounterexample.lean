import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesComplexCayleyCounterexample

def actualImaginarySkew : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of (fun _ _ => Complex.I)

def actualComplexCayley (skew : Matrix (Fin 1) (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  (1-skew)*(1+skew)⁻¹

theorem actual_imaginary_matrix_is_skew_hermitian :
    actualImaginarySkewᴴ= -actualImaginarySkew := by
  ext i j
  fin_cases i
  fin_cases j
  simp [actualImaginarySkew]

theorem actual_imaginary_cayley_denominator_inverse :
    (1+actualImaginarySkew)⁻¹=
      Matrix.of (fun _ _ => ((1-Complex.I)/2:ℂ)) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  simp [actualImaginarySkew,Matrix.mul_apply,Fin.sum_univ_one,Matrix.add_apply]
  ring_nf
  simp [Complex.I_sq] <;> norm_num <;> ring

theorem actual_imaginary_cayley_is_negative_imaginary :
    actualComplexCayley actualImaginarySkew=
      Matrix.of (fun _ _ => (-Complex.I:ℂ)) := by
  unfold actualComplexCayley
  rw [actual_imaginary_cayley_denominator_inverse]
  ext i j
  fin_cases i
  fin_cases j
  simp [actualImaginarySkew,Matrix.mul_apply,Fin.sum_univ_one,Matrix.sub_apply]
  ring_nf
  simp [Complex.I_sq] <;> ring

theorem actual_imaginary_cayley_is_unitary :
    (actualComplexCayley actualImaginarySkew)ᴴ*
      actualComplexCayley actualImaginarySkew=1 := by
  rw [actual_imaginary_cayley_is_negative_imaginary]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply,Fin.sum_univ_one,Complex.I_sq]

theorem actual_imaginary_cayley_determinant_is_not_one :
    (actualComplexCayley actualImaginarySkew).det= -Complex.I ∧
      (actualComplexCayley actualImaginarySkew).det≠1 := by
  rw [actual_imaginary_cayley_is_negative_imaginary,Matrix.det_fin_one]
  constructor
  · rfl
  · intro he
    have hreal := congrArg Complex.re he
    norm_num at hreal

theorem actual_complex_skew_cayley_does_not_preserve_real_determinant_claim :
    ¬ ∀ skew : Matrix (Fin 1) (Fin 1) ℂ, skewᴴ= -skew →
      (actualComplexCayley skew).det=1 := by
  intro hclaim
  exact actual_imaginary_cayley_determinant_is_not_one.2
    (hclaim actualImaginarySkew actual_imaginary_matrix_is_skew_hermitian)

end SafeLearning.CompleteModulesComplexCayleyCounterexample
