import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsFunctionInverseRange

def rangeRestricted {X Y : Type*} (f : X → Y) (x : X) : Set.range f :=
  ⟨f x, ⟨x, rfl⟩⟩

theorem actual_range_restricted_map_is_bijective_iff_original_is_injective
    {X Y : Type*} (f : X → Y) :
    Function.Bijective (rangeRestricted f) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    apply h.1
    exact Subtype.ext hxy
  · intro h
    constructor
    · intro x y hxy
      exact h (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x,hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩

theorem actual_strictly_increasing_function_has_a_true_inverse_on_its_actual_range
    {X Y : Type*} [LinearOrder X] [Preorder Y]
    (f : X → Y) (hf : StrictMono f) :
    ∃ inverse : Set.range f → X,
      (∀ x, inverse (rangeRestricted f x) = x) ∧
        (∀ y : Set.range f, rangeRestricted f (inverse y) = y) := by
  apply Function.bijective_iff_has_inverse.mp
  exact actual_range_restricted_map_is_bijective_iff_original_is_injective f |>.mpr hf.injective

theorem actual_range_inverse_solves_the_original_function_equation
    {X Y : Type*} [LinearOrder X] [Preorder Y]
    (f : X → Y) (hf : StrictMono f) :
    ∃ inverse : Set.range f → X,
      (∀ x, inverse (rangeRestricted f x) = x) ∧
        (∀ y : Set.range f, f (inverse y) = y.val) := by
  obtain ⟨inverse,hi,hr⟩ :=
    actual_strictly_increasing_function_has_a_true_inverse_on_its_actual_range f hf
  exact ⟨inverse, hi, fun y => congrArg Subtype.val (hr y)⟩

end SafeLearning.CompleteFoundationsFunctionInverseRange
