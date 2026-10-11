import SafeLearning.CompleteModulesFIROperator
import SafeLearning.CompleteModulesFIRGain
import SafeLearning.CompleteModulesFIRNumbers
import SafeLearning.CompleteModulesCayleyPlane

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRParameterization
open CompleteModulesFIRBase CompleteModulesFIROperator CompleteModulesFIRGain CompleteModulesFIRNumbers
  CompleteModulesCayleyPlane

def actualParameterFactor (gain storage : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![Real.sqrt storage,Real.sqrt (gain^2-storage)]

def actualParameterUnitVector (angle : ℝ) : Fin 2 → ℝ := ![Real.cos angle,Real.sin angle]

theorem actual_parameter_vector_is_unit (angle : ℝ) :
    ∑ coordinate,(actualParameterUnitVector angle coordinate)^2=1 := by
  simpa [actualParameterUnitVector,Fin.sum_univ_two] using Real.cos_sq_add_sin_sq angle

theorem actual_parameter_factor_gram_is_source_dissipation_matrix
    (gain storage : ℝ) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    (actualParameterFactor gain storage)ᵀ*actualParameterFactor gain storage=
      actualFIRDissipationMatrix gain storage := by
  rw [actual_fir_dissipation_matrix_is_source_diagonal]
  simp only [pow_two] at hupper
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [actualParameterFactor,Matrix.mul_apply,Fin.sum_univ_two,pow_two,
      Real.mul_self_sqrt hstorage,Real.mul_self_sqrt (sub_nonneg.mpr hupper)]

theorem actual_parameterized_row_is_the_actual_kernel_row
    (gain storage angle : ℝ) :
    actualUnitRow (actualParameterUnitVector angle)*actualParameterFactor gain storage=
      actualFIRKernelRow (actualParameterizedCurrentKernel gain storage angle)
        (actualParameterizedDelayedKernel storage angle) := by
  ext row column
  fin_cases row
  fin_cases column <;> simp [actualUnitRow,actualParameterUnitVector,actualParameterFactor,
    actualFIRKernelRow,actualParameterizedCurrentKernel,actualParameterizedDelayedKernel,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.replicateRow_apply]

theorem actual_parameterized_fir_certificate_is_positive_semidefinite
    (gain storage angle : ℝ) (hstorage : 0 ≤ storage) (hupper : storage ≤ gain^2) :
    (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow (actualParameterizedCurrentKernel gain storage angle)
        (actualParameterizedDelayedKernel storage angle))ᵀ*
        actualFIRKernelRow (actualParameterizedCurrentKernel gain storage angle)
          (actualParameterizedDelayedKernel storage angle)).PosSemidef := by
  have h := actual_unit_row_cholesky_certificate_is_positive_semidefinite
    (actualParameterUnitVector angle) (actual_parameter_vector_is_unit angle) (actualParameterFactor gain storage)
  rwa [actual_parameter_factor_gram_is_source_dissipation_matrix gain storage hstorage hupper,
    actual_parameterized_row_is_the_actual_kernel_row] at h

theorem actual_source_unit_vector_is_produced_by_actual_cayley :
    ∀ coordinate : Fin 2,
    (CompleteModulesCayley.actualCayley (actualPlaneSkew ((Real.sqrt 3)⁻¹))) coordinate 0=
      actualParameterUnitVector (Real.pi/3) coordinate := by
  rw [actual_plane_cayley_is_rotation,Real.arctan_inv_sqrt_three]
  have ha : 2*(Real.pi/6)=Real.pi/3 := by ring
  rw [ha]
  intro coordinate
  fin_cases coordinate <;> simp [actualPlaneRotation,actualParameterUnitVector]

theorem actual_source_kernel_row_is_the_unit_factor_parameterization :
    actualUnitRow (actualParameterUnitVector (Real.pi/3))*actualSourceCholesky=actualSourceKernelRow := by
  obtain ⟨hdelayed,hcurrent⟩ := actual_source_trigonometric_kernel_is_exact_radical
  ext row column
  fin_cases row
  fin_cases column
  · simpa [actualUnitRow,actualParameterUnitVector,actualSourceCholesky,actualSourceKernelRow,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.replicateRow_apply,div_eq_mul_inv] using hdelayed
  · simpa [actualUnitRow,actualParameterUnitVector,actualSourceCholesky,actualSourceKernelRow,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.replicateRow_apply,div_eq_mul_inv] using hcurrent

theorem actual_source_exact_certificate_is_positive_semidefinite : actualExactCertificate.PosSemidef := by
  have h := actual_unit_row_cholesky_certificate_is_positive_semidefinite
    (actualParameterUnitVector (Real.pi/3)) (actual_parameter_vector_is_unit _) actualSourceCholesky
  rwa [actual_source_cholesky_is_exact_positive_factor.1,
    actual_source_kernel_row_is_the_unit_factor_parameterization] at h

theorem actual_source_certificate_characteristic_polynomial :
    actualExactCertificate.charpoly=X*(X-C (1/2:ℝ)) := by
  rw [Matrix.charpoly_fin_two,actual_source_certificate_determinant_and_trace.1,
    actual_source_certificate_determinant_and_trace.2]
  simp only [map_zero,add_zero]
  ring

theorem actual_source_certificate_eigenvalues (eigenvalue : ℝ) :
    eigenvalue ∈ spectrum ℝ actualExactCertificate ↔ eigenvalue=0 ∨ eigenvalue=1/2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,actual_source_certificate_characteristic_polynomial]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_source_frequency_supremum_is_exact_gain :
    sSup (Set.range (fun frequency : ℝ => ‖actualFIRTransfer actualCurrentKernel actualDelayedKernel frequency‖))=
      (Real.sqrt 2+Real.sqrt 6)/4 := by
  rw [actual_positive_fir_frequency_supremum actualCurrentKernel actualDelayedKernel
    (by unfold actualCurrentKernel;positivity) (by unfold actualDelayedKernel;positivity),
    actual_source_frequency_gain_value_and_rounding.1]

end SafeLearning.CompleteModulesFIRParameterization
