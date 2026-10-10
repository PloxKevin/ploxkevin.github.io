import SafeLearning.CompleteModulesGeneralRoesserSignals

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGeneralRoesserMatrices
open CompleteModulesGeneralRoesserSignals
variable {I O C : Type*} [Fintype I] [Fintype O] [Fintype C]
  [DecidableEq I] [DecidableEq O] [DecidableEq C]

def actualUpperDelayMatrix (radius : ℕ) : Matrix (Fin radius × C) (Fin radius × C) ℝ :=
  fun row column => if column.1.val=row.1.val+1 then (if column.2=row.2 then 1 else 0) else 0

def actualLowerDelayMatrix (radius : ℕ) : Matrix (Fin radius × C) (Fin radius × C) ℝ :=
  fun row column => if row.1.val=column.1.val+1 then (if column.2=row.2 then 1 else 0) else 0

def actualFirstDelayInjection (radius : ℕ) : Matrix (Fin radius × C) C ℝ :=
  fun row column => if row.1.val=0 then (if column=row.2 then 1 else 0) else 0

def actualFirstDelaySelection (radius : ℕ) : Matrix C (Fin radius × C) ℝ :=
  fun row column => if column.1.val=0 then (if column.2=row then 1 else 0) else 0

theorem actual_upper_delay_matrix_action (radius : ℕ) (vector : Fin radius × C → ℝ)
    (row : Fin radius × C) :
    (actualUpperDelayMatrix radius*ᵥvector) row=
      if h : row.1.val+1<radius then vector (⟨row.1.val+1,h⟩,row.2) else 0 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actualUpperDelayMatrix]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  split_ifs with h
  · have hc (column : Fin radius) : (column.val=row.1.val+1) ↔ column=⟨row.1.val+1,h⟩ := by
      constructor
      · intro he; exact Fin.ext he
      · intro he; exact congrArg Fin.val he
    simp_rw [hc]
    simp
  · have hc (column : Fin radius) : column.val≠row.1.val+1 := by have hh:=column.isLt; omega
    simp [hc]

theorem actual_lower_delay_matrix_action (radius : ℕ) (vector : Fin radius × C → ℝ)
    (row : Fin radius × C) :
    (actualLowerDelayMatrix radius*ᵥvector) row=
      if h : row.1.val=0 then 0 else vector (⟨row.1.val-1,by have hr:=row.1.isLt; omega⟩,row.2) := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actualLowerDelayMatrix]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  split_ifs with h
  · simp [h]
  · have hc (column : Fin radius) : (row.1.val=column.val+1) ↔
        column=⟨row.1.val-1,by have hr:=row.1.isLt; omega⟩ := by
      rw [Fin.ext_iff]
      change (row.1.val=column.val+1) ↔ column.val=row.1.val-1
      omega
    simp_rw [hc]
    simp

theorem actual_first_delay_injection_action (radius : ℕ) (input : C → ℝ)
    (row : Fin radius × C) :
    (actualFirstDelayInjection radius*ᵥinput) row=
      if row.1.val=0 then input row.2 else 0 := by
  simp [actualFirstDelayInjection,Matrix.mulVec,dotProduct,ite_mul,Finset.sum_ite_irrel]

theorem actual_first_delay_selection_action (radius : ℕ) (vector : Fin radius × C → ℝ)
    (output : C) :
    (actualFirstDelaySelection radius*ᵥvector) output=
      if h : 0<radius then vector (⟨0,h⟩,output) else 0 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actualFirstDelaySelection]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  split_ifs with h
  · have hc (column : Fin radius) : (column.val=0) ↔ column=⟨0,h⟩ := by
      constructor
      · intro he; exact Fin.ext he
      · intro he; exact congrArg Fin.val he
    simp_rw [hc]
    simp
  · have hc (column : Fin radius) : column.val≠0 := by have hh:=column.isLt; omega
    simp [hc]

def actualGeneralRoesserA12 (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ) :
    Matrix (Fin verticalRadius × O) (Fin horizontalRadius × I) ℝ :=
  fun row column => kernel (row.1.val+1) (column.1.val+1) row.2 column.2

def actualGeneralRoesserB1 (verticalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ) :
    Matrix (Fin verticalRadius × O) I ℝ := fun row column => kernel (row.1.val+1) 0 row.2 column

def actualGeneralRoesserC2 (horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ) :
    Matrix O (Fin horizontalRadius × I) ℝ := fun row column => kernel 0 (column.1.val+1) row column.2

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_general_roesser_cross_matrix_action
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) (row : Fin verticalRadius × O) :
    (actualGeneralRoesserA12 verticalRadius horizontalRadius kernel*ᵥ
      actualGeneralHorizontalState horizontalRadius input vertical horizontal) row=
        (∑ delay ∈ Finset.range horizontalRadius,kernel (row.1.val+1) (delay+1)*ᵥ
          input vertical (horizontal-(delay+1 : ℕ))) row.2 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actualGeneralRoesserA12,
    actualGeneralHorizontalState,actualGeneralHorizontalComponent,Finset.sum_apply]
  exact Fin.sum_univ_eq_sum_range (fun delay => ∑ channel : I,
    kernel (row.1.val+1) (delay+1) row.2 channel*input vertical (horizontal-(delay+1 : ℕ)) channel) horizontalRadius

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_general_roesser_vertical_input_matrix_action
    (verticalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : I → ℝ) (row : Fin verticalRadius × O) :
    (actualGeneralRoesserB1 verticalRadius kernel*ᵥinput) row=
      (kernel (row.1.val+1) 0*ᵥinput) row.2 := by rfl

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem actual_general_roesser_horizontal_output_matrix_action
    (horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) (output : O) :
    (actualGeneralRoesserC2 horizontalRadius kernel*ᵥ
      actualGeneralHorizontalState horizontalRadius input vertical horizontal) output=
        (∑ delay ∈ Finset.range horizontalRadius,kernel 0 (delay+1)*ᵥ
          input vertical (horizontal-(delay+1 : ℕ))) output := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,actualGeneralRoesserC2,
    actualGeneralHorizontalState,actualGeneralHorizontalComponent,Finset.sum_apply]
  exact Fin.sum_univ_eq_sum_range (fun delay => ∑ channel : I,
    kernel 0 (delay+1) output channel*input vertical (horizontal-(delay+1 : ℕ)) channel) horizontalRadius

end SafeLearning.CompleteModulesGeneralRoesserMatrices
