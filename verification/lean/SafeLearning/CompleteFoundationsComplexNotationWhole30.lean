import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace SafeLearning.CompleteFoundationsComplexNotation30

theorem actual_complex_cartesian_coordinates (z : ℂ) :
    z = (z.re : ℂ) + (z.im : ℂ) * Complex.I :=
  z.re_add_im.symm

theorem actual_imaginary_unit_square : Complex.I ^ 2 = (-1 : ℂ) :=
  Complex.I_sq

theorem actual_conjugate_cartesian_coordinates (a b : ℝ) :
    conj ((a : ℂ) + (b : ℂ) * Complex.I) = (a : ℂ) - (b : ℂ) * Complex.I := by
  simp [map_add,map_mul,sub_eq_add_neg]

theorem actual_modulus_square_is_conjugate_product (z : ℂ) :
    z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) :=
  by simpa only [Complex.ofReal_pow] using Complex.mul_conj' z

theorem actual_modulus_is_nonnegative_real_square_root (z : ℂ) :
    (z * conj z).im = 0 ∧ 0 ≤ (z * conj z).re ∧
      ‖z‖ = Real.sqrt (z * conj z).re := by
  refine ⟨?_,?_,?_⟩
  · rw [actual_modulus_square_is_conjugate_product]
    rfl
  · rw [actual_modulus_square_is_conjugate_product]
    change 0 ≤ ‖z‖ ^ 2
    exact sq_nonneg _
  · rw [actual_modulus_square_is_conjugate_product]
    change ‖z‖ = Real.sqrt (‖z‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg z)).symm

theorem actual_Euler_formula_for_every_real_angle (theta : ℝ) :
    Complex.exp ((theta : ℂ) * Complex.I) =
      (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I := by
  simp [Complex.exp_mul_I]

theorem actual_every_complex_number_has_polar_form (z : ℂ) :
    ∃ r theta : ℝ, 0 ≤ r ∧
      z = (r : ℂ) * Complex.exp ((theta : ℂ) * Complex.I) ∧
      z = (r : ℂ) * ((Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I) := by
  refine ⟨‖z‖,z.arg,norm_nonneg z,(Complex.norm_mul_exp_arg_mul_I z).symm,?_⟩
  rw [← actual_Euler_formula_for_every_real_angle]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

def actualColumn {n : Type*} (v : n → ℂ) : Matrix n (Fin 1) ℂ := fun i _ => v i

def actualVectorSquaredModulus {n : Type*} [Fintype n] (v : n → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

theorem actual_vector_adjoint_is_conjugate_transpose
    {n : Type*} (v : n → ℂ) (i : n) :
    (actualColumn v).conjTranspose 0 i = conj (v i) := rfl

theorem actual_vector_adjoint_product_is_sum_of_squared_moduli
    {n : Type*} [Fintype n] (v : n → ℂ) :
    ((actualColumn v).conjTranspose * actualColumn v) 0 0 =
      (actualVectorSquaredModulus v : ℂ) := by
  classical
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,actualColumn]
  simp only [Complex.star_def,Complex.conj_mul']
  simp only [actualVectorSquaredModulus,Complex.ofReal_sum,Complex.ofReal_pow]

theorem actual_vector_squared_modulus_positive_iff_nonzero
    {n : Type*} [Fintype n] (v : n → ℂ) :
    0 < actualVectorSquaredModulus v ↔ v ≠ 0 := by
  classical
  constructor
  · intro h hv
    subst v
    simp [actualVectorSquaredModulus] at h
  · intro hv
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
    have hn : v i ≠ 0 := by simpa using hi
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖v j‖)
      ⟨i,Finset.mem_univ i,sq_pos_of_pos (norm_pos_iff.mpr hn)⟩

def actualRealRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos theta,-Real.sin theta;Real.sin theta,Real.cos theta]

def actualComplexRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos theta : ℂ),-(Real.sin theta : ℂ);
     (Real.sin theta : ℂ),(Real.cos theta : ℂ)]

theorem actual_rotation_is_the_complexified_real_matrix (theta : ℝ) :
    (actualRealRotation theta).map (algebraMap ℝ ℂ) = actualComplexRotation theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [actualRealRotation,actualComplexRotation]

theorem actual_negative_angle_Euler_formula (theta : ℝ) :
    Complex.exp (-(theta : ℂ) * Complex.I) =
      (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I := by
  simpa only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,neg_mul,sub_eq_add_neg]
    using actual_Euler_formula_for_every_real_angle (-theta)

theorem actual_rotation_positive_angle_eigenvector (theta : ℝ) :
    (![1,-Complex.I] : Fin 2 → ℂ) ≠ 0 ∧
      actualComplexRotation theta *ᵥ ![1,-Complex.I] =
        Complex.exp ((theta : ℂ) * Complex.I) • ![1,-Complex.I] := by
  constructor
  · intro h
    have := congrFun h 0
    norm_num at this
  · rw [actual_Euler_formula_for_every_real_angle]
    ext i
    fin_cases i <;>
      simp [actualComplexRotation,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq]

theorem actual_rotation_negative_angle_eigenvector (theta : ℝ) :
    (![1,Complex.I] : Fin 2 → ℂ) ≠ 0 ∧
      actualComplexRotation theta *ᵥ ![1,Complex.I] =
        Complex.exp (-(theta : ℂ) * Complex.I) • ![1,Complex.I] := by
  constructor
  · intro h
    have := congrFun h 0
    norm_num at this
  · rw [actual_negative_angle_Euler_formula]
    ext i
    fin_cases i <;>
      simp [actualComplexRotation,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq]

theorem actual_rotation_characteristic_polynomial (theta : ℝ) :
    (actualComplexRotation theta).charpoly =
      (Polynomial.X-Polynomial.C (Complex.exp ((theta : ℂ)*Complex.I))) *
      (Polynomial.X-Polynomial.C (Complex.exp (-(theta : ℂ)*Complex.I))) := by
  rw [Matrix.charpoly_fin_two,actual_Euler_formula_for_every_real_angle,
    actual_negative_angle_Euler_formula]
  simp [actualComplexRotation,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
  ring_nf
  have hI : (Polynomial.C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
    rw [← Polynomial.C_pow,Complex.I_sq]
    simp
  rw [hI]
  ring

theorem actual_rotation_all_complex_eigenvalues (theta : ℝ) (z : ℂ) :
    z ∈ spectrum ℂ (actualComplexRotation theta) ↔
      z = Complex.exp ((theta : ℂ)*Complex.I) ∨
      z = Complex.exp (-(theta : ℂ)*Complex.I) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,actual_rotation_characteristic_polynomial]
  simp [Polynomial.IsRoot,mul_eq_zero,sub_eq_zero]

theorem actual_rotation_eigenvalue_multiset_including_repeated_values (theta : ℝ) :
    (actualComplexRotation theta).charpoly.roots =
      {Complex.exp ((theta : ℂ)*Complex.I),Complex.exp (-(theta : ℂ)*Complex.I)} := by
  rw [actual_rotation_characteristic_polynomial,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _))]
  simp

end SafeLearning.CompleteFoundationsComplexNotation30
