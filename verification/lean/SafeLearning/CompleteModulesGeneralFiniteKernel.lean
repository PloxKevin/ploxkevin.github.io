import SafeLearning.CompleteModulesGeneralRoesserRealization

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGeneralFiniteKernel
open CompleteModulesGeneralRoesserSignals CompleteModulesGeneralRoesserMatrices
open CompleteModulesGeneralRoesserRealization
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem actual_source_three_by_five_correct_and_swapped_counts_differ :
    Fintype.card ((Fin 2 × Fin 32) ⊕ (Fin 4 × Fin 16))=128 ∧
    Fintype.card ((Fin 2 × Fin 16) ⊕ (Fin 4 × Fin 32))=160 ∧ (128:ℕ)<160 := by
  norm_num

def actualFiniteKernelZeroExtension (verticalRadius horizontalRadius : ℕ)
    (kernel : Fin (verticalRadius+1) → Fin (horizontalRadius+1) → Matrix O I ℝ)
    (row column : ℕ) : Matrix O I ℝ :=
  if hr : row < verticalRadius+1 then
    if hc : column < horizontalRadius+1 then kernel ⟨row,hr⟩ ⟨column,hc⟩ else 0
  else 0

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_finite_kernel_extension_recovers_every_kernel_entry
    (verticalRadius horizontalRadius : ℕ)
    (kernel : Fin (verticalRadius+1) → Fin (horizontalRadius+1) → Matrix O I ℝ)
    (row : Fin (verticalRadius+1)) (column : Fin (horizontalRadius+1)) :
    actualFiniteKernelZeroExtension verticalRadius horizontalRadius kernel row.val column.val=
      kernel row column := by
  simp [actualFiniteKernelZeroExtension,row.isLt,column.isLt]

def actualSourceFiniteKernelConvolution (verticalRadius horizontalRadius : ℕ)
    (kernel : Fin (verticalRadius+1) → Fin (horizontalRadius+1) → Matrix O I ℝ)
    (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) : O → ℝ :=
  bias+∑ row : Fin (verticalRadius+1),∑ column : Fin (horizontalRadius+1),
    kernel row column*ᵥactualFinitePaddedNaturalImage image vertical horizontal row.val column.val

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_finite_kernel_source_convolution_is_the_bounded_natural_sum
    (verticalRadius horizontalRadius : ℕ)
    (kernel : Fin (verticalRadius+1) → Fin (horizontalRadius+1) → Matrix O I ℝ)
    (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) :
    actualFiniteSourceConvolution verticalRadius horizontalRadius
      (actualFiniteKernelZeroExtension verticalRadius horizontalRadius kernel) bias image vertical horizontal=
        actualSourceFiniteKernelConvolution verticalRadius horizontalRadius kernel bias image vertical horizontal := by
  unfold actualFiniteSourceConvolution actualSourceFiniteKernelConvolution
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro row _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro column _
  rw [actual_finite_kernel_extension_recovers_every_kernel_entry]

omit [DecidableEq I] in
theorem actual_all_finite_kernels_have_the_source_roesser_output
    (verticalRadius horizontalRadius : ℕ)
    (kernel : Fin (verticalRadius+1) → Fin (horizontalRadius+1) → Matrix O I ℝ)
    (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) :
    let extendedKernel := actualFiniteKernelZeroExtension verticalRadius horizontalRadius kernel
    let extendedImage := actualNaturalImageZeroExtension image
    actualFirstDelaySelection verticalRadius*ᵥactualGeneralVerticalState verticalRadius horizontalRadius
      extendedKernel extendedImage vertical horizontal+
      actualGeneralRoesserC2 horizontalRadius extendedKernel*ᵥactualGeneralHorizontalState horizontalRadius
        extendedImage vertical horizontal+
      extendedKernel 0 0*ᵥextendedImage vertical horizontal+bias=
        actualSourceFiniteKernelConvolution verticalRadius horizontalRadius kernel bias image vertical horizontal := by
  dsimp only
  rw [actual_general_roesser_output_recovers_source_natural_image_convolution,
    actual_finite_kernel_source_convolution_is_the_bounded_natural_sum]

omit [DecidableEq O] in
theorem actual_general_horizontal_roesser_has_zero_vertical_cross_block
    (verticalRadius horizontalRadius : ℕ)
    (kernel : ℕ → ℕ → Matrix O I ℝ) (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualGeneralHorizontalState horizontalRadius input vertical (horizontal+1)=
      (0 : Matrix (Fin horizontalRadius × I) (Fin verticalRadius × O) ℝ)*ᵥ
        actualGeneralVerticalState verticalRadius horizontalRadius kernel input vertical horizontal+
      actualLowerDelayMatrix horizontalRadius*ᵥactualGeneralHorizontalState horizontalRadius input vertical horizontal+
      actualFirstDelayInjection horizontalRadius*ᵥinput vertical horizontal := by
  simpa only [zero_mulVec,zero_add] using
    actual_general_roesser_horizontal_matrix_recursion horizontalRadius input vertical horizontal

end SafeLearning.CompleteModulesGeneralFiniteKernel
