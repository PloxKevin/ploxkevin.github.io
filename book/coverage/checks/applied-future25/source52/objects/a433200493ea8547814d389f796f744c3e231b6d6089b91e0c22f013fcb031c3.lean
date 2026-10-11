import SafeLearning.CompleteModulesRoesserThreeByThree

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRoesserPadding
open CompleteModulesThreeTapConvolution CompleteModulesRoesserThreeByThree
variable {I O R : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] [Field R]

def actualPaddedImageSample (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ)
    (verticalDelay horizontalDelay : Fin 3) : I → R :=
  if verticalDelay.val ≤ vertical ∧ horizontalDelay.val ≤ horizontal then
    input (vertical-verticalDelay.val) (horizontal-horizontalDelay.val) else 0

theorem actual_roesser_output_equals_literal_double_convolution
    (kernel : Fin 3 → Fin 3 → Matrix O I R) (bias : O → R) (input : ℕ → ℕ → I → R)
    (vertical horizontal : ℕ) :
    actualZeroPaddedThreeByThreeConvolution kernel bias input vertical horizontal=
      bias+∑ verticalDelay : Fin 3,∑ horizontalDelay : Fin 3,
        kernel verticalDelay horizontalDelay *ᵥ
          actualPaddedImageSample input vertical horizontal verticalDelay horizontalDelay := by
  ext coordinate
  rcases vertical with (_|(_|vertical)) <;> rcases horizontal with (_|(_|horizontal)) <;>
    simp (disch := omega) [actualZeroPaddedThreeByThreeConvolution,actualHorizontalRowResponse,
      actualPreviousSignal,actualPaddedImageSample,Fin.sum_univ_three] <;> abel

theorem actual_previous_zero_signal_is_zero :
    actualPreviousSignal (0 : ℕ → O → R)=0 := by
  ext time coordinate
  cases time <;> rfl

theorem actual_zero_three_by_three_kernel_output_is_bias
    (bias : O → R) (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) :
    actualZeroPaddedThreeByThreeConvolution (0 : Fin 3 → Fin 3 → Matrix O I R) bias input vertical horizontal=bias := by
  rw [actual_roesser_output_equals_literal_double_convolution]
  simp

theorem actual_zero_kernel_has_genuine_empty_state_realization
    (bias : O → R) (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) :
    (0 : Fin 0 → R)=
      (0 : Matrix (Fin 0) (Fin 0) R) *ᵥ (0 : Fin 0 → R)+
      (0 : Matrix (Fin 0) (Fin 0) R) *ᵥ (0 : Fin 0 → R)+
      (0 : Matrix (Fin 0) I R) *ᵥ input vertical horizontal ∧
    (0 : Matrix O (Fin 0) R) *ᵥ (0 : Fin 0 → R)+
      (0 : Matrix O (Fin 0) R) *ᵥ (0 : Fin 0 → R)+
      (0 : Matrix O I R) *ᵥ input vertical horizontal+bias=
      actualZeroPaddedThreeByThreeConvolution (0 : Fin 3 → Fin 3 → Matrix O I R) bias input vertical horizontal := by
  simp [actual_zero_three_by_three_kernel_output_is_bias]

theorem actual_zero_kernel_empty_realization_has_strictly_fewer_than_source_states :
    Fintype.card (Sum (Fin 0) (Fin 0)) <
      Fintype.card (Sum (Sum (Fin 32) (Fin 32)) (Sum (Fin 16) (Fin 16))) := by
  norm_num

end SafeLearning.CompleteModulesRoesserPadding
