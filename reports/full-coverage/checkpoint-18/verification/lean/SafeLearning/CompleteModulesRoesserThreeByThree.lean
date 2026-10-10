import SafeLearning.CompleteModulesThreeTapConvolution

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRoesserThreeByThree
open CompleteModulesThreeTapConvolution
variable {I O R : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] [Field R]

def actualHorizontalRowResponse (kernel : Fin 3 → Fin 3 → Matrix O I R)
    (delay : Fin 3) (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) : O → R :=
  kernel delay 0 *ᵥ input vertical horizontal+
    kernel delay 1 *ᵥ actualPreviousSignal (input vertical) horizontal+
    kernel delay 2 *ᵥ actualPreviousSignal (actualPreviousSignal (input vertical)) horizontal

def actualRoesserVerticalState (kernel : Fin 3 → Fin 3 → Matrix O I R)
    (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) : Sum O O → R :=
  Sum.elim
    (actualPreviousSignal (fun v => actualHorizontalRowResponse kernel 2 input v horizontal) vertical)
    (actualPreviousSignal (actualPreviousSignal (fun v => actualHorizontalRowResponse kernel 2 input v horizontal)) vertical+
      actualPreviousSignal (fun v => actualHorizontalRowResponse kernel 1 input v horizontal) vertical)

def actualRoesserHorizontalState (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) : Sum I I → R :=
  Sum.elim (actualPreviousSignal (actualPreviousSignal (input vertical)) horizontal)
    (actualPreviousSignal (input vertical) horizontal)

def actualRoesserA11 : Matrix (Sum O O) (Sum O O) R := Matrix.fromBlocks 0 0 1 0

def actualRoesserA12 (kernel : Fin 3 → Fin 3 → Matrix O I R) : Matrix (Sum O O) (Sum I I) R :=
  Matrix.fromBlocks (kernel 2 2) (kernel 2 1) (kernel 1 2) (kernel 1 1)

def actualRoesserA22 : Matrix (Sum I I) (Sum I I) R := Matrix.fromBlocks 0 1 0 0

def actualRoesserB1 (kernel : Fin 3 → Fin 3 → Matrix O I R) : Matrix (Sum O O) I R :=
  Matrix.fromRows (kernel 2 0) (kernel 1 0)

def actualRoesserB2 : Matrix (Sum I I) I R := Matrix.fromRows 0 1

def actualRoesserC1 : Matrix O (Sum O O) R := Matrix.fromCols 0 1

def actualRoesserC2 (kernel : Fin 3 → Fin 3 → Matrix O I R) : Matrix O (Sum I I) R :=
  Matrix.fromCols (kernel 0 2) (kernel 0 1)

def actualZeroPaddedThreeByThreeConvolution (kernel : Fin 3 → Fin 3 → Matrix O I R)
    (bias : O → R) (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) : O → R :=
  bias+actualHorizontalRowResponse kernel 0 input vertical horizontal+
    actualPreviousSignal (fun v => actualHorizontalRowResponse kernel 1 input v horizontal) vertical+
    actualPreviousSignal (actualPreviousSignal (fun v => actualHorizontalRowResponse kernel 2 input v horizontal)) vertical

theorem actual_roesser_vertical_zero_boundary (kernel : Fin 3 → Fin 3 → Matrix O I R)
    (input : ℕ → ℕ → I → R) (horizontal : ℕ) :
    actualRoesserVerticalState kernel input 0 horizontal=0 := by
  ext coordinate
  cases coordinate <;> simp [actualRoesserVerticalState,actualPreviousSignal]

theorem actual_roesser_horizontal_zero_boundary (input : ℕ → ℕ → I → R) (vertical : ℕ) :
    actualRoesserHorizontalState input vertical 0=0 := by
  ext coordinate
  cases coordinate <;> simp [actualRoesserHorizontalState,actualPreviousSignal]

theorem actual_roesser_vertical_state_space_recursion (kernel : Fin 3 → Fin 3 → Matrix O I R)
    (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) :
    actualRoesserVerticalState kernel input (vertical+1) horizontal=
      (actualRoesserA11 : Matrix (Sum O O) (Sum O O) R) *ᵥ actualRoesserVerticalState kernel input vertical horizontal+
      actualRoesserA12 kernel *ᵥ actualRoesserHorizontalState input vertical horizontal+
      actualRoesserB1 kernel *ᵥ input vertical horizontal := by
  simp only [actualRoesserA11,actualRoesserA12,actualRoesserB1,Matrix.fromBlocks_mulVec,Matrix.fromRows_mulVec]
  ext coordinate
  cases coordinate <;> simp [actualRoesserVerticalState,actualRoesserHorizontalState,actualHorizontalRowResponse,
    actualPreviousSignal,Function.comp_def] <;> abel

theorem actual_roesser_horizontal_state_space_recursion (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) :
    actualRoesserHorizontalState input vertical (horizontal+1)=
      (actualRoesserA22 : Matrix (Sum I I) (Sum I I) R) *ᵥ actualRoesserHorizontalState input vertical horizontal+
      actualRoesserB2 *ᵥ input vertical horizontal := by
  simp only [actualRoesserA22,actualRoesserB2,Matrix.fromBlocks_mulVec,Matrix.fromRows_mulVec]
  ext coordinate
  cases coordinate <;> simp [actualRoesserHorizontalState,actualPreviousSignal,Function.comp_def]

theorem actual_roesser_output_is_zero_padded_three_by_three_convolution
    (kernel : Fin 3 → Fin 3 → Matrix O I R) (bias : O → R) (input : ℕ → ℕ → I → R) (vertical horizontal : ℕ) :
    (actualRoesserC1 : Matrix O (Sum O O) R) *ᵥ actualRoesserVerticalState kernel input vertical horizontal+
      actualRoesserC2 kernel *ᵥ actualRoesserHorizontalState input vertical horizontal+
      kernel 0 0 *ᵥ input vertical horizontal+bias=
    actualZeroPaddedThreeByThreeConvolution kernel bias input vertical horizontal := by
  simp only [actualRoesserC1,actualRoesserC2,Matrix.fromCols_mulVec]
  simp only [actualRoesserVerticalState,actualRoesserHorizontalState,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,Matrix.one_mulVec,zero_add,actualZeroPaddedThreeByThreeConvolution,actualHorizontalRowResponse]
  ext coordinate
  simp only [Pi.add_apply]
  abel

theorem actual_roesser_three_by_three_state_dimensions :
    Fintype.card (Sum O O)=2*Fintype.card O ∧ Fintype.card (Sum I I)=2*Fintype.card I := by
  simp only [Fintype.card_sum]
  constructor <;> omega

theorem actual_source_sixteen_to_thirty_two_channel_roesser_state_count :
    Fintype.card (Sum (Fin 32) (Fin 32))=64 ∧
    Fintype.card (Sum (Fin 16) (Fin 16))=32 ∧
    Fintype.card (Sum (Sum (Fin 32) (Fin 32)) (Sum (Fin 16) (Fin 16)))=96 := by
  norm_num

end SafeLearning.CompleteModulesRoesserThreeByThree
