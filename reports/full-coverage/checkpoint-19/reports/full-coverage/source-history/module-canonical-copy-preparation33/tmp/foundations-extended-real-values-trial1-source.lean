import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsExtendedRealValues

theorem actual_every_extended_real_is_a_real_or_an_infinite_endpoint (a : EReal) :
    a = ⊥ ∨ a = ⊤ ∨ ∃ r : ℝ, a = (r : EReal) := by
  induction a using EReal.rec with
  | bot => exact Or.inl rfl
  | coe r => exact Or.inr (Or.inr ⟨r,rfl⟩)
  | top => exact Or.inr (Or.inl rfl)

theorem actual_extended_supremum_and_infimum_always_exist (A : Set EReal) :
    IsLUB A (sSup A) ∧ IsGLB A (sInf A) := ⟨isLUB_sSup A,isGLB_sInf A⟩

theorem actual_empty_extended_extrema_have_the_printed_infinite_values :
    sSup (∅ : Set EReal) = ⊥ ∧ sInf (∅ : Set EReal) = ⊤ ∧
      upperBounds (∅ : Set EReal) = univ ∧ lowerBounds (∅ : Set EReal) = univ := by
  simp

theorem actual_real_unbounded_above_sets_have_extended_supremum_infinity
    (A : Set ℝ) (hA : ¬BddAbove A) :
    sSup ((fun r : ℝ => (r : EReal)) '' A) = ⊤ := by
  by_contra hn
  obtain ⟨b,hb,_⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hn)
  apply hA
  refine ⟨b,?_⟩
  intro a ha
  exact (EReal.coe_lt_coe_iff.mp ((le_sSup (mem_image_of_mem _ ha)).trans_lt hb)).le

theorem actual_real_unbounded_below_sets_have_extended_infimum_negative_infinity
    (A : Set ℝ) (hA : ¬BddBelow A) :
    sInf ((fun r : ℝ => (r : EReal)) '' A) = ⊥ := by
  by_contra hn
  obtain ⟨b,_,hb⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hn)
  apply hA
  refine ⟨b,?_⟩
  intro a ha
  exact (EReal.coe_lt_coe_iff.mp (hb.trans_le (sInf_le (mem_image_of_mem _ ha)))).le

theorem actual_adding_positive_infinity_has_the_printed_nonindeterminate_value
    (a : EReal) (ha : a ≠ ⊥) : a + ⊤ = ⊤ := EReal.add_top_of_ne_bot ha

/-- The ordinary partial sum does not assign a value to opposite infinite endpoints. -/
def partialAdd (a b : EReal) : Option EReal :=
  if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then none else some (a+b)

def partialSubtract (a b : EReal) : Option EReal := partialAdd a (-b)

theorem actual_partial_extended_arithmetic_keeps_infinity_minus_infinity_undefined :
    partialSubtract ⊤ ⊤ = none ∧ partialSubtract ⊥ ⊥ = none ∧
      (∀ r : ℝ, partialAdd r ⊤ = some ⊤) ∧
      ∀ a : EReal, a ≠ ⊥ → partialAdd a ⊤ = some ⊤ := by
  constructor
  · simp [partialSubtract,partialAdd]
  constructor
  · simp [partialSubtract,partialAdd]
  constructor
  · intro r
    simp [partialAdd]
  · intro a ha
    simp [partialAdd,ha,EReal.add_top_of_ne_bot ha]

def minimizationValue {X : Type*} (f : X → EReal) (S : Set X) : EReal := sInf (f '' S)

theorem actual_infeasible_minimization_has_value_positive_infinity
    {X : Type*} (f : X → EReal) : minimizationValue f ∅ = ⊤ := by
  simp [minimizationValue]

theorem actual_unbounded_below_real_minimization_has_value_negative_infinity
    {X : Type*} (f : X → ℝ) (S : Set X) (h : ¬BddBelow (f '' S)) :
    minimizationValue (fun x => (f x : EReal)) S = ⊥ := by
  unfold minimizationValue
  rw [← image_image]
  exact actual_real_unbounded_below_sets_have_extended_infimum_negative_infinity (f '' S) h

def proper {X : Type*} (f : X → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

theorem actual_properness_is_never_negative_infinity_and_finite_somewhere
    {X : Type*} (f : X → EReal) :
    proper f ↔ (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊥ ∧ f x ≠ ⊤ := by
  constructor
  · rintro ⟨ha,x,r,hr⟩
    exact ⟨ha,x,hr ▸ EReal.coe_ne_bot r,hr ▸ EReal.coe_ne_top r⟩
  · rintro ⟨ha,x,hbot,htop⟩
    refine ⟨ha,x,?_⟩
    rcases actual_every_extended_real_is_a_real_or_an_infinite_endpoint (f x) with h | h | h
    · exact (hbot h).elim
    · exact (htop h).elim
    · exact h

end SafeLearning.CompleteFoundationsExtendedRealValues
