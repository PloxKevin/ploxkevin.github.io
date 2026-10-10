import SafeLearning.CompleteFoundationsExtendedRealValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsExtendedSupremumRules
open SafeLearning.CompleteFoundationsExtendedRealValues

def realImageSup {X : Type*} (f : X → ℝ) : EReal := sSup (range (fun x => (f x : EReal)))
def realImageInf {X : Type*} (f : X → ℝ) : EReal := sInf (range (fun x => (f x : EReal)))

theorem actual_real_valued_function_suprema_and_infima_do_not_need_boundedness
    {X : Type*} (f : X → ℝ) :
    IsLUB (range (fun x => (f x : EReal))) (realImageSup f) ∧
      IsGLB (range (fun x => (f x : EReal))) (realImageInf f) :=
  ⟨isLUB_sSup _,isGLB_sInf _⟩

theorem actual_extended_pointwise_sum_supremum_and_infimum_have_the_printed_directions
    {X : Type*} (f g : X → ℝ) :
    realImageSup (fun x => f x+g x) ≤ realImageSup f+realImageSup g ∧
      realImageInf f+realImageInf g ≤ realImageInf (fun x => f x+g x) := by
  constructor
  · apply sSup_le
    rintro z ⟨x,rfl⟩
    simpa only [EReal.coe_add] using
      add_le_add (le_sSup (mem_range_self x)) (le_sSup (mem_range_self x))
  · apply le_sInf
    rintro z ⟨x,rfl⟩
    simpa only [EReal.coe_add] using
      add_le_add (sInf_le (mem_range_self x)) (sInf_le (mem_range_self x))

theorem actual_nonempty_real_valued_function_suprema_are_never_negative_infinity
    {X : Type*} [Nonempty X] (f : X → ℝ) : realImageSup f ≠ ⊥ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact (lt_of_lt_of_le (EReal.bot_lt_coe (f x)) (le_sSup (mem_range_self x))).ne'

theorem actual_nonempty_real_valued_function_infima_are_never_positive_infinity
    {X : Type*} [Nonempty X] (f : X → ℝ) : realImageInf f ≠ ⊤ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact (lt_of_le_of_lt (sInf_le (mem_range_self x)) (EReal.coe_lt_top (f x))).ne

theorem actual_source_supremum_and_infimum_sums_are_defined_for_real_valued_functions
    {X : Type*} [Nonempty X] (f g : X → ℝ) :
    partialAdd (realImageSup f) (realImageSup g) = some (realImageSup f+realImageSup g) ∧
      partialAdd (realImageInf f) (realImageInf g) = some (realImageInf f+realImageInf g) := by
  constructor
  · simp [partialAdd,actual_nonempty_real_valued_function_suprema_are_never_negative_infinity]
  · simp [partialAdd,actual_nonempty_real_valued_function_infima_are_never_positive_infinity]

theorem actual_arbitrary_real_functions_have_extended_max_min_below_min_max
    {X Y : Type*} (phi : X → Y → ℝ) :
    (⨆ y, ⨅ x, (phi x y : EReal)) ≤ ⨅ x, ⨆ y, (phi x y : EReal) :=
  iSup_iInf_le_iInf_iSup (fun y x => (phi x y : EReal))

theorem actual_extended_extrema_are_monotone_under_set_inclusion
    (A B : Set EReal) (hab : A ⊆ B) : sSup A ≤ sSup B ∧ sInf B ≤ sInf A :=
  ⟨sSup_le_sSup hab,sInf_le_sInf hab⟩

end SafeLearning.CompleteFoundationsExtendedSupremumRules
