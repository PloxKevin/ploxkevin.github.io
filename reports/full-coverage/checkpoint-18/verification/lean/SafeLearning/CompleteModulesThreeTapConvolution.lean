import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesThreeTapConvolution
variable {I O R : Type*} [Fintype I] [Fintype O] [DecidableEq I] [Field R]

def actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R :=
  Matrix.fromBlocks 0 0 1 0

def actualThreeTapInputMatrix : Matrix (Sum I I) I R := Matrix.fromRows 1 0

def actualThreeTapOutputMatrix (delayed twiceDelayed : Matrix O I R) : Matrix O (Sum I I) R :=
  Matrix.fromCols delayed twiceDelayed

def actualPreviousSignal (input : ℕ → I → R) : ℕ → I → R
  | 0 => 0
  | time+1 => input time

def actualThreeTapState (input : ℕ → I → R) (time : ℕ) : Sum I I → R :=
  Sum.elim (actualPreviousSignal input time) (actualPreviousSignal (actualPreviousSignal input) time)

def actualThreeTapConvolution (current delayed twiceDelayed : Matrix O I R)
    (bias : O → R) (input : ℕ → I → R) (time : ℕ) : O → R :=
  bias+current *ᵥ input time+delayed *ᵥ actualPreviousSignal input time+
    twiceDelayed *ᵥ actualPreviousSignal (actualPreviousSignal input) time

theorem actual_three_tap_state_matrix_action (state : Sum I I → R) :
    (actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R) *ᵥ state=
      Sum.elim (0 : I → R) (fun coordinate => state (Sum.inl coordinate)) := by
  simp [actualThreeTapStateMatrix,Matrix.fromBlocks_mulVec,Function.comp_def]

theorem actual_three_tap_input_matrix_action (input : I → R) :
    (actualThreeTapInputMatrix : Matrix (Sum I I) I R) *ᵥ input=Sum.elim input 0 := by
  simp [actualThreeTapInputMatrix]

theorem actual_three_tap_state_space_recursion (input : ℕ → I → R) :
    actualThreeTapState input 0=0 ∧
    ∀ time,actualThreeTapState input (time+1)=
      (actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R) *ᵥ actualThreeTapState input time+
      actualThreeTapInputMatrix *ᵥ input time := by
  constructor
  · ext coordinate
    cases coordinate <;> simp [actualThreeTapState,actualPreviousSignal]
  · intro time
    rw [actual_three_tap_state_matrix_action,actual_three_tap_input_matrix_action]
    ext coordinate
    cases coordinate <;> simp [actualThreeTapState,actualPreviousSignal]

theorem actual_three_tap_output_matrix_action (delayed twiceDelayed : Matrix O I R) (state : Sum I I → R) :
    actualThreeTapOutputMatrix delayed twiceDelayed *ᵥ state=
      delayed *ᵥ (fun coordinate => state (Sum.inl coordinate))+
      twiceDelayed *ᵥ (fun coordinate => state (Sum.inr coordinate)) := by
  ext coordinate
  simp [actualThreeTapOutputMatrix,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromCols]

theorem actual_three_tap_state_space_output_is_zero_padded_convolution
    (current delayed twiceDelayed : Matrix O I R) (bias : O → R) (input : ℕ → I → R) (time : ℕ) :
    actualThreeTapOutputMatrix delayed twiceDelayed *ᵥ actualThreeTapState input time+
      current *ᵥ input time+bias=actualThreeTapConvolution current delayed twiceDelayed bias input time := by
  rw [actual_three_tap_output_matrix_action]
  simp only [actualThreeTapState,Sum.elim_inl,Sum.elim_inr,actualThreeTapConvolution]
  abel

theorem actual_three_tap_state_matrix_squared_is_zero :
    (actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R)^2=0 := by
  rw [pow_two]
  simp [actualThreeTapStateMatrix,Matrix.fromBlocks_multiply]

end SafeLearning.CompleteModulesThreeTapConvolution
