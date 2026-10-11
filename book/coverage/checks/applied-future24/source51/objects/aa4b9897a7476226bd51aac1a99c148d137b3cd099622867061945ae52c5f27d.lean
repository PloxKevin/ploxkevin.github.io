import SafeLearning.CompleteModulesGeneralRoesserMatrices

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGeneralRoesserRealization
open CompleteModulesGeneralRoesserSignals CompleteModulesGeneralRoesserMatrices
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

omit [DecidableEq I] in
theorem actual_general_vertical_shift_matrix_action
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) (row : Fin verticalRadius × O) :
    (actualUpperDelayMatrix verticalRadius*ᵥ
      actualGeneralVerticalState verticalRadius horizontalRadius kernel input vertical horizontal) row=
        actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input (row.1.val+1) vertical horizontal row.2 := by
  rw [actual_upper_delay_matrix_action]
  split_ifs with h
  · rfl
  · simp [actualGeneralVerticalComponent,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]

omit [DecidableEq I] in
theorem actual_general_vertical_output_selection_matrix_action
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) (output : O) :
    (actualFirstDelaySelection verticalRadius*ᵥ
      actualGeneralVerticalState verticalRadius horizontalRadius kernel input vertical horizontal) output=
        actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input 0 vertical horizontal output := by
  rw [actual_first_delay_selection_action]
  split_ifs with h
  · rfl
  · have hr : verticalRadius=0 := by omega
    simp [actualGeneralVerticalComponent,hr]

omit [DecidableEq I] in
theorem actual_general_roesser_vertical_matrix_recursion
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualGeneralVerticalState verticalRadius horizontalRadius kernel input (vertical+1) horizontal=
      actualUpperDelayMatrix verticalRadius*ᵥactualGeneralVerticalState verticalRadius horizontalRadius kernel input vertical horizontal+
        actualGeneralRoesserA12 verticalRadius horizontalRadius kernel*ᵥactualGeneralHorizontalState horizontalRadius input vertical horizontal+
        actualGeneralRoesserB1 verticalRadius kernel*ᵥinput vertical horizontal := by
  ext row
  simp only [Pi.add_apply]
  change actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input row.1.val (vertical+1) horizontal row.2= _
  rw [actual_general_vertical_shift_matrix_action,actual_general_roesser_cross_matrix_action,
    actual_general_roesser_vertical_input_matrix_action]
  have hr := congrFun (actual_general_vertical_components_have_true_delay_recursion
    verticalRadius horizontalRadius kernel input row.1.val vertical horizontal) row.2
  simp only [ite_eq_left row.1.isLt,actualGeneralRowResponse,Pi.add_apply] at hr
  linarith only [hr]

theorem actual_general_roesser_horizontal_matrix_recursion
    (horizontalRadius : ℕ) (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualGeneralHorizontalState horizontalRadius input vertical (horizontal+1)=
      actualLowerDelayMatrix horizontalRadius*ᵥactualGeneralHorizontalState horizontalRadius input vertical horizontal+
        actualFirstDelayInjection horizontalRadius*ᵥinput vertical horizontal := by
  ext row
  simp only [Pi.add_apply]
  rw [actual_lower_delay_matrix_action,actual_first_delay_injection_action]
  have hr := congrFun (actual_general_horizontal_components_have_true_delay_recursion
    input row.1.val vertical horizontal) row.2
  split_ifs with h
  · simpa only [actualGeneralHorizontalState,ite_eq_left h,zero_add] using hr
  · simpa only [actualGeneralHorizontalState,ite_eq_right h,add_zero] using hr

omit [DecidableEq I] in
theorem actual_general_roesser_output_is_full_kernel_convolution
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (bias : O → ℝ) (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualFirstDelaySelection verticalRadius*ᵥactualGeneralVerticalState verticalRadius horizontalRadius kernel input vertical horizontal+
      actualGeneralRoesserC2 horizontalRadius kernel*ᵥactualGeneralHorizontalState horizontalRadius input vertical horizontal+
      kernel 0 0*ᵥinput vertical horizontal+bias=
        actualGeneralZeroPaddedConvolution verticalRadius horizontalRadius kernel bias input vertical horizontal := by
  rw [actual_general_convolution_output_is_direct_term_plus_vertical_component]
  ext output
  simp only [Pi.add_apply]
  rw [actual_general_vertical_output_selection_matrix_action,actual_general_roesser_horizontal_output_matrix_action]
  simp only [actualGeneralRowResponse,Pi.add_apply]
  ring

omit [DecidableEq I] in
theorem actual_general_roesser_output_recovers_source_natural_image_convolution
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) :
    actualFirstDelaySelection verticalRadius*ᵥactualGeneralVerticalState verticalRadius horizontalRadius kernel
      (actualNaturalImageZeroExtension image) vertical horizontal+
      actualGeneralRoesserC2 horizontalRadius kernel*ᵥactualGeneralHorizontalState horizontalRadius
        (actualNaturalImageZeroExtension image) vertical horizontal+
      kernel 0 0*ᵥactualNaturalImageZeroExtension image vertical horizontal+bias=
        actualFiniteSourceConvolution verticalRadius horizontalRadius kernel bias image vertical horizontal := by
  rw [actual_general_roesser_output_is_full_kernel_convolution,
    actual_general_signed_convolution_recovers_source_natural_convolution]

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_general_roesser_source_vertical_boundary
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (image : ℕ → ℕ → I → ℝ) (horizontal : ℤ) :
    actualGeneralVerticalState verticalRadius horizontalRadius kernel (actualNaturalImageZeroExtension image) 0 horizontal=0 := by
  apply actual_general_vertical_state_has_true_zero_boundary
  intro vertical horizontal hv
  exact actual_natural_image_extension_is_zero_padded image vertical horizontal (Or.inl hv)

omit [Fintype I] [DecidableEq I] in
theorem actual_general_roesser_source_horizontal_boundary
    (horizontalRadius : ℕ) (image : ℕ → ℕ → I → ℝ) (vertical : ℤ) :
    actualGeneralHorizontalState horizontalRadius (actualNaturalImageZeroExtension image) vertical 0=0 := by
  apply actual_general_horizontal_state_has_true_zero_boundary
  intro vertical horizontal hh
  exact actual_natural_image_extension_is_zero_padded image vertical horizontal (Or.inr hh)

end SafeLearning.CompleteModulesGeneralRoesserRealization
