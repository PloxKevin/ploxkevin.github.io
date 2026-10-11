import SafeLearning.CompleteModulesFIRParameterization
import SafeLearning.CompleteModulesFIRInfinite

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRCorollaries
open CompleteModulesFIRBase CompleteModulesFIROperator CompleteModulesFIRGain CompleteModulesFIRNumbers
  CompleteModulesFIRParameterization CompleteModulesFIRInfinite

theorem actual_source_cholesky_is_lower_and_upper_triangular :
    actualSourceCholesky.IsLowerTriangular ∧ actualSourceCholesky.IsUpperTriangular := by
  constructor
  · intro row column h
    change row < column at h
    simp [actualSourceCholesky,Matrix.one_apply,ne_of_lt h]
  · intro row column h
    change column < row at h
    simp [actualSourceCholesky,Matrix.one_apply,(ne_of_lt h).symm]

theorem actual_positive_regularizer_or_nonzero_free_parameter_gives_interior_storage
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain) (hregularizer : 0 ≤ regularizer)
    (hstrict : 0 < regularizer ∨ freeParameter≠0) :
    (0 < actualFIRStorage gain freeParameter regularizer ∧ actualFIRStorage gain freeParameter regularizer < gain^2) ∧
    (actualFIRDissipationMatrix gain (actualFIRStorage gain freeParameter regularizer)).PosDef := by
  have hp : 0 < freeParameter^2+regularizer := by
    rcases hstrict with hr|hf
    · nlinarith [sq_nonneg freeParameter]
    · nlinarith [sq_pos_of_ne_zero hf]
  exact ⟨actual_fir_storage_strictly_between_zero_and_gain_squared gain freeParameter regularizer hgain hregularizer hp,
    actual_fir_dissipation_matrix_is_positive_definite gain freeParameter regularizer hgain hregularizer hp⟩

theorem actual_source_half_factor_is_exact_cholesky :
    actualParameterFactor 1 (1/2)=actualSourceCholesky := by
  have hs : Real.sqrt (1/2)=1/Real.sqrt 2 := by
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [eq_div_iff hp.ne']
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 1/2 by norm_num)]
    norm_num
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [actualParameterFactor,actualSourceCholesky,hs]

theorem actual_source_radical_kernels_are_actual_parameterized_kernels :
    actualParameterizedCurrentKernel 1 (1/2) (Real.pi/3)=actualCurrentKernel ∧
    actualParameterizedDelayedKernel (1/2) (Real.pi/3)=actualDelayedKernel := by
  have hr := actual_parameterized_row_is_the_actual_kernel_row 1 (1/2) (Real.pi/3)
  rw [actual_source_half_factor_is_exact_cholesky,
    actual_source_kernel_row_is_the_unit_factor_parameterization] at hr
  constructor
  · have he := congrArg (fun row : Matrix (Fin 1) (Fin 2) ℝ => row 0 1) hr
    simpa [actualSourceKernelRow,actualFIRKernelRow] using he.symm
  · have he := congrArg (fun row : Matrix (Fin 1) (Fin 2) ℝ => row 0 0) hr
    simpa [actualSourceKernelRow,actualFIRKernelRow] using he.symm

theorem actual_source_unit_storage_radical_kernel_certificate :
    (actualFIRDissipationMatrix 1 (actualFIRStorage 1 1 0)-
      (actualFIRKernelRow actualCurrentKernel actualDelayedKernel)ᵀ*
        actualFIRKernelRow actualCurrentKernel actualDelayedKernel).PosSemidef := by
  rw [actual_fir_source_unit_parameters.2.2]
  exact actual_source_exact_certificate_is_positive_semidefinite

theorem actual_source_radical_filter_has_actual_storage_dissipation
    (state input : ℝ) :
    (1/2:ℝ)*input^2-(1/2:ℝ)*state^2 ≤ input^2-(actualFIROutput actualCurrentKernel actualDelayedKernel state input)^2 := by
  have h := actual_fir_certificate_implies_storage_dissipation 1 (actualFIRStorage 1 1 0)
    actualCurrentKernel actualDelayedKernel actual_source_unit_storage_radical_kernel_certificate state input
  simpa only [actual_fir_source_unit_parameters.2.1,one_pow,one_mul] using h

theorem actual_source_radical_filter_has_actual_finite_energy_bound
    (input : ℕ → ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(actualFIRResponse actualCurrentKernel actualDelayedKernel input time)^2) ≤
      (∑ time ∈ Finset.range horizon,(input time)^2) := by
  have h := actual_zero_initial_fir_output_energy_bound 1 (actualFIRStorage 1 1 0)
    actualCurrentKernel actualDelayedKernel (by rw [actual_fir_source_unit_parameters.2.1];norm_num)
    actual_source_unit_storage_radical_kernel_certificate input horizon
  simpa using h

theorem actual_source_radical_filter_has_actual_infinite_energy_bound
    (input : ℕ → ℝ) (hinput : Summable (fun time => (input time)^2)) :
    Summable (fun time => (actualFIRResponse actualCurrentKernel actualDelayedKernel input time)^2) ∧
    (∑' time,(actualFIRResponse actualCurrentKernel actualDelayedKernel input time)^2) ≤
      (∑' time,(input time)^2) := by
  have h := actual_fir_square_summable_input_has_bounded_square_summable_output 1 (actualFIRStorage 1 1 0)
    actualCurrentKernel actualDelayedKernel (by rw [actual_fir_source_unit_parameters.2.1];norm_num)
    actual_source_unit_storage_radical_kernel_certificate input hinput
  simpa using h

end SafeLearning.CompleteModulesFIRCorollaries
