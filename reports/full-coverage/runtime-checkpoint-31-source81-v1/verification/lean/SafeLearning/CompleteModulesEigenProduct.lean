import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace SafeLearning.CompleteModulesEigenProduct

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualComplexEigenvalues (matrix : Matrix N N ℂ) : Multiset ℂ := matrix.charpoly.roots

theorem actual_constant_multiset_product (values : Multiset ℂ) (constant : ℂ) :
    (values.map (fun _ => constant)).prod=constant^values.card := by
  induction values using Multiset.induction_on with
  | empty => simp
  | cons value values ih => simp [ih,pow_succ,mul_comm]

theorem actual_complex_characteristic_roots_count (matrix : Matrix N N ℂ) :
    (actualComplexEigenvalues matrix).card=Fintype.card N := by
  unfold actualComplexEigenvalues
  rw [← (IsAlgClosed.splits matrix.charpoly).natDegree_eq_card_roots,
    Matrix.charpoly_natDegree_eq_dim]

theorem actual_complex_determinant_is_eigenvalue_product
    (matrix : Matrix N N ℂ) (step : ℂ) :
    (1+step • matrix).det=
      ((actualComplexEigenvalues matrix).map (fun eigenvalue => 1+step*eigenvalue)).prod := by
  by_cases hstep : step=0
  · subst step
    simp
  · have hmatrix : (-step) • (Matrix.scalar N (-step⁻¹)-matrix)=1+step • matrix := by
      ext i j
      simp [Matrix.scalar,Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,
        Matrix.diagonal_apply,Matrix.one_apply]
      split_ifs <;> field_simp <;> ring
    have hsplit := IsAlgClosed.splits matrix.charpoly
    have hproduct := hsplit.eval_eq_prod_roots_of_monic matrix.charpoly_monic (-step⁻¹)
    have he : (1+step • matrix).det=(-step)^(Fintype.card N)*matrix.charpoly.eval (-step⁻¹) := by
      rw [← hmatrix,Matrix.det_smul,Matrix.eval_charpoly]
    rw [he,hproduct]
    change (-step)^Fintype.card N*((actualComplexEigenvalues matrix).map (fun value => -step⁻¹-value)).prod=_
    calc
      _ = ((actualComplexEigenvalues matrix).map (fun _ => -step)).prod*
          ((actualComplexEigenvalues matrix).map (fun value => -step⁻¹-value)).prod := by
        rw [actual_constant_multiset_product,actual_complex_characteristic_roots_count]
      _ = ((actualComplexEigenvalues matrix).map (fun value => (-step)*(-step⁻¹-value))).prod := by
        rw [Multiset.prod_map_mul]
      _ = _ := by
        have hf : (fun value : ℂ => (-step)*(-step⁻¹-value))=
            (fun value : ℂ => 1+step*value) := by
          funext value
          field_simp
          ring
        rw [hf]

def complexification (matrix : Matrix N N ℝ) : Matrix N N ℂ := matrix.map Complex.ofRealHom

theorem actual_real_determinant_is_actual_complex_eigenvalue_product
    (matrix : Matrix N N ℝ) (step : ℝ) :
    ((1+step • matrix).det : ℂ)=
      ((actualComplexEigenvalues (complexification matrix)).map
        (fun eigenvalue => 1+(step:ℂ)*eigenvalue)).prod := by
  have he : (1+step • matrix).map Complex.ofRealHom=
      (1 : Matrix N N ℂ)+(step:ℂ) • complexification matrix := by
    ext i j
    simp [complexification,Matrix.map_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply]
    split_ifs <;> simp
  have h := actual_complex_determinant_is_eigenvalue_product (complexification matrix) (step:ℂ)
  rw [← he] at h
  have hdet := (RingHom.map_det Complex.ofRealHom (1+step • matrix)).symm
  change ((1+step • matrix).map Complex.ofRealHom).det=
    Complex.ofRealHom (1+step • matrix).det at hdet
  rw [hdet] at h
  exact h

theorem actual_characteristic_root_is_actual_matrix_spectral_value
    (matrix : Matrix N N ℂ) (eigenvalue : ℂ)
    (hroot : eigenvalue ∈ actualComplexEigenvalues matrix) : eigenvalue ∈ spectrum ℂ matrix := by
  apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
  exact (Polynomial.mem_roots matrix.charpoly_monic.ne_zero).mp hroot

end SafeLearning.CompleteModulesEigenProduct
