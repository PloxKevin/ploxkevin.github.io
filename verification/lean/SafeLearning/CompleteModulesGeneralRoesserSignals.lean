import SafeLearning.CompleteModulesRoesserThreeByThree

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGeneralRoesserSignals
variable {I O : Type*} [Fintype I] [Fintype O]

def actualGeneralRowResponse (horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (rowDelay : ℕ) (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) : O → ℝ :=
  kernel rowDelay 0*ᵥinput vertical horizontal+
    ∑ delay ∈ Finset.range horizontalRadius,kernel rowDelay (delay+1)*ᵥinput vertical (horizontal-(delay+1 : ℕ))

def actualGeneralVerticalComponent (verticalRadius horizontalRadius : ℕ)
    (kernel : ℕ → ℕ → Matrix O I ℝ) (input : ℤ → ℤ → I → ℝ)
    (slot : ℕ) (vertical horizontal : ℤ) : O → ℝ :=
  ∑ delay ∈ Finset.range (verticalRadius-slot),
    actualGeneralRowResponse horizontalRadius kernel (slot+1+delay) input (vertical-(delay+1 : ℕ)) horizontal

def actualGeneralHorizontalComponent (input : ℤ → ℤ → I → ℝ)
    (slot : ℕ) (vertical horizontal : ℤ) : I → ℝ :=
  input vertical (horizontal-(slot+1 : ℕ))

def actualGeneralVerticalState (verticalRadius horizontalRadius : ℕ)
    (kernel : ℕ → ℕ → Matrix O I ℝ) (input : ℤ → ℤ → I → ℝ)
    (vertical horizontal : ℤ) : Fin verticalRadius × O → ℝ :=
  fun coordinate => actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input
    coordinate.1.val vertical horizontal coordinate.2

def actualGeneralHorizontalState (horizontalRadius : ℕ) (input : ℤ → ℤ → I → ℝ)
    (vertical horizontal : ℤ) : Fin horizontalRadius × I → ℝ :=
  fun coordinate => actualGeneralHorizontalComponent input coordinate.1.val vertical horizontal coordinate.2

def actualGeneralZeroPaddedConvolution (verticalRadius horizontalRadius : ℕ)
    (kernel : ℕ → ℕ → Matrix O I ℝ) (bias : O → ℝ) (input : ℤ → ℤ → I → ℝ)
    (vertical horizontal : ℤ) : O → ℝ :=
  bias+∑ row ∈ Finset.range (verticalRadius+1),
    ∑ column ∈ Finset.range (horizontalRadius+1),kernel row column*ᵥinput (vertical-row) (horizontal-column)

omit [Fintype O] in
theorem actual_general_row_response_is_full_horizontal_convolution
    (horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ) (rowDelay : ℕ)
    (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualGeneralRowResponse horizontalRadius kernel rowDelay input vertical horizontal=
      ∑ column ∈ Finset.range (horizontalRadius+1),kernel rowDelay column*ᵥinput vertical (horizontal-column) := by
  rw [Finset.sum_range_succ']
  simp only [actualGeneralRowResponse,Nat.cast_zero,sub_zero]
  exact add_comm _ _

omit [Fintype O] in
theorem actual_general_vertical_components_have_true_delay_recursion
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (slot : ℕ) (vertical horizontal : ℤ) :
    actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input slot (vertical+1) horizontal=
      if slot<verticalRadius then
        actualGeneralRowResponse horizontalRadius kernel (slot+1) input vertical horizontal+
          actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input (slot+1) vertical horizontal
      else 0 := by
  by_cases hslot : slot<verticalRadius
  · rw [ite_eq_left hslot]
    have he : verticalRadius-slot=(verticalRadius-(slot+1))+1 := by omega
    unfold actualGeneralVerticalComponent
    rw [he,Finset.sum_range_succ']
    simp only [Nat.add_zero,Nat.zero_add,Nat.cast_one,add_sub_cancel_right]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro delay _
    have hrow : slot+1+(delay+1)=(slot+1)+1+delay := by omega
    have hv : vertical+1-(delay+1+1 : ℕ)=vertical-(delay+1 : ℕ) := by push_cast; ring
    rw [hrow,hv]
  · rw [ite_eq_right hslot]
    simp [actualGeneralVerticalComponent,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hslot)]

omit [Fintype I] in
theorem actual_general_horizontal_components_have_true_delay_recursion
    (input : ℤ → ℤ → I → ℝ) (slot : ℕ) (vertical horizontal : ℤ) :
    actualGeneralHorizontalComponent input slot vertical (horizontal+1)=
      if slot=0 then input vertical horizontal else
        actualGeneralHorizontalComponent input (slot-1) vertical horizontal := by
  by_cases hslot : slot=0
  · subst slot
    simp [actualGeneralHorizontalComponent]
  · rw [ite_eq_right hslot]
    have he : slot-1+1=slot := by omega
    unfold actualGeneralHorizontalComponent
    rw [he]
    have hh : horizontal+1-(slot+1 : ℕ)=horizontal-slot := by push_cast; ring
    rw [hh]

omit [Fintype O] in
theorem actual_general_convolution_output_is_direct_term_plus_vertical_component
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (bias : O → ℝ) (input : ℤ → ℤ → I → ℝ) (vertical horizontal : ℤ) :
    actualGeneralZeroPaddedConvolution verticalRadius horizontalRadius kernel bias input vertical horizontal=
      bias+actualGeneralRowResponse horizontalRadius kernel 0 input vertical horizontal+
        actualGeneralVerticalComponent verticalRadius horizontalRadius kernel input 0 vertical horizontal := by
  unfold actualGeneralZeroPaddedConvolution
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,sub_zero]
  simp_rw [← actual_general_row_response_is_full_horizontal_convolution]
  unfold actualGeneralVerticalComponent
  simp only [Nat.sub_zero,Nat.zero_add,add_comm (1:ℕ)]
  abel

omit [Fintype O] in
theorem actual_general_negative_vertical_row_response_vanishes
    (horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ) (rowDelay : ℕ)
    (input : ℤ → ℤ → I → ℝ) (hpadding : ∀ vertical horizontal,vertical<0 → input vertical horizontal=0)
    (vertical horizontal : ℤ) (hvertical : vertical<0) :
    actualGeneralRowResponse horizontalRadius kernel rowDelay input vertical horizontal=0 := by
  unfold actualGeneralRowResponse
  simp [hpadding vertical _ hvertical]

omit [Fintype O] in
theorem actual_general_vertical_state_has_true_zero_boundary
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (input : ℤ → ℤ → I → ℝ) (hpadding : ∀ vertical horizontal,vertical<0 → input vertical horizontal=0)
    (horizontal : ℤ) : actualGeneralVerticalState verticalRadius horizontalRadius kernel input 0 horizontal=0 := by
  ext coordinate
  unfold actualGeneralVerticalState actualGeneralVerticalComponent
  simp only [Pi.zero_apply,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro delay _
  rw [actual_general_negative_vertical_row_response_vanishes _ _ _ _ hpadding]
  · rfl
  · have hd : (0:ℤ) ≤ delay := Int.natCast_nonneg delay
    push_cast
    omega

omit [Fintype I] in
theorem actual_general_horizontal_state_has_true_zero_boundary
    (horizontalRadius : ℕ) (input : ℤ → ℤ → I → ℝ)
    (hpadding : ∀ vertical horizontal,horizontal<0 → input vertical horizontal=0)
    (vertical : ℤ) : actualGeneralHorizontalState horizontalRadius input vertical 0=0 := by
  ext coordinate
  unfold actualGeneralHorizontalState actualGeneralHorizontalComponent
  have hh : (0:ℤ)-(coordinate.1.val+1 : ℕ)<0 := by push_cast; omega
  rw [hpadding _ _ hh]
  rfl

theorem actual_general_roesser_directional_state_dimensions
    (verticalRadius horizontalRadius : ℕ) :
    Fintype.card (Fin verticalRadius × O)=verticalRadius*Fintype.card O ∧
      Fintype.card (Fin horizontalRadius × I)=horizontalRadius*Fintype.card I := by
  simp

theorem actual_source_three_by_five_channel_state_count :
    Fintype.card (Fin 2 × Fin 32)=64 ∧ Fintype.card (Fin 4 × Fin 16)=64 ∧
      Fintype.card ((Fin 2 × Fin 32) ⊕ (Fin 4 × Fin 16))=128 := by norm_num

def actualNaturalImageZeroExtension (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℤ) : I → ℝ :=
  if 0 ≤ vertical ∧ 0 ≤ horizontal then image vertical.toNat horizontal.toNat else 0

omit [Fintype I] in
theorem actual_natural_image_extension_is_zero_padded
    (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℤ) :
    vertical<0 ∨ horizontal<0 → actualNaturalImageZeroExtension image vertical horizontal=0 := by
  intro h
  unfold actualNaturalImageZeroExtension
  apply ite_eq_right
  rcases h with hv | hh <;> intro hn <;> linarith [hn.1,hn.2]

omit [Fintype I] in
theorem actual_natural_image_extension_recovers_original_nonnegative_image
    (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) :
    actualNaturalImageZeroExtension image vertical horizontal=image vertical horizontal := by
  simp [actualNaturalImageZeroExtension]

def actualFinitePaddedNaturalImage (image : ℕ → ℕ → I → ℝ)
    (vertical horizontal rowDelay columnDelay : ℕ) : I → ℝ :=
  if rowDelay ≤ vertical ∧ columnDelay ≤ horizontal then image (vertical-rowDelay) (horizontal-columnDelay) else 0

omit [Fintype I] in
theorem actual_signed_delay_coordinates_are_true_finite_zero_padding
    (image : ℕ → ℕ → I → ℝ) (vertical horizontal rowDelay columnDelay : ℕ) :
    actualNaturalImageZeroExtension image ((vertical : ℤ)-rowDelay) ((horizontal : ℤ)-columnDelay)=
      actualFinitePaddedNaturalImage image vertical horizontal rowDelay columnDelay := by
  by_cases h : rowDelay ≤ vertical ∧ columnDelay ≤ horizontal
  · have hv : ((vertical : ℤ)-rowDelay)=((vertical-rowDelay : ℕ) : ℤ) := by exact (Nat.cast_sub h.1).symm
    have hh : ((horizontal : ℤ)-columnDelay)=((horizontal-columnDelay : ℕ) : ℤ) := by exact (Nat.cast_sub h.2).symm
    rw [hv,hh,actual_natural_image_extension_recovers_original_nonnegative_image]
    simp [actualFinitePaddedNaturalImage,h]
  · have hz : ((vertical : ℤ)-rowDelay)<0 ∨ ((horizontal : ℤ)-columnDelay)<0 := by
      omega
    rw [actual_natural_image_extension_is_zero_padded image _ _ hz]
    simp [actualFinitePaddedNaturalImage,h]

def actualFiniteSourceConvolution (verticalRadius horizontalRadius : ℕ)
    (kernel : ℕ → ℕ → Matrix O I ℝ) (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ)
    (vertical horizontal : ℕ) : O → ℝ :=
  bias+∑ row ∈ Finset.range (verticalRadius+1),∑ column ∈ Finset.range (horizontalRadius+1),
    kernel row column*ᵥactualFinitePaddedNaturalImage image vertical horizontal row column

omit [Fintype O] in
theorem actual_general_signed_convolution_recovers_source_natural_convolution
    (verticalRadius horizontalRadius : ℕ) (kernel : ℕ → ℕ → Matrix O I ℝ)
    (bias : O → ℝ) (image : ℕ → ℕ → I → ℝ) (vertical horizontal : ℕ) :
    actualGeneralZeroPaddedConvolution verticalRadius horizontalRadius kernel bias
      (actualNaturalImageZeroExtension image) vertical horizontal=
        actualFiniteSourceConvolution verticalRadius horizontalRadius kernel bias image vertical horizontal := by
  simp only [actualGeneralZeroPaddedConvolution,actualFiniteSourceConvolution,
    actual_signed_delay_coordinates_are_true_finite_zero_padding]

end SafeLearning.CompleteModulesGeneralRoesserSignals
