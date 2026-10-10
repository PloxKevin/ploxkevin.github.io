import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsEquilibriumShift

def shiftedUpdate {E : Type*} [AddCommGroup E] (F : E → E) (equilibrium : E)
    (coordinate : E) : E := F (coordinate + equilibrium) - equilibrium

def shiftedConstraint {E : Type*} [AddCommGroup E] (original : Set E)
    (equilibrium : E) : Set E := {coordinate | coordinate + equilibrium ∈ original}

def shiftedStorage {E : Type*} [AddCommGroup E] (V : E → ℝ)
    (equilibrium : E) (coordinate : E) : ℝ := V (coordinate + equilibrium)

theorem actual_translation_to_and_from_equilibrium_coordinates
    {E : Type*} [AddCommGroup E] (equilibrium state coordinate : E) :
    (state - equilibrium) + equilibrium = state ∧
      (coordinate + equilibrium) - equilibrium = coordinate := by
  simp

theorem actual_equilibrium_becomes_a_true_origin_fixed_point
    {E : Type*} [AddCommGroup E] (F : E → E) (equilibrium : E)
    (he : F equilibrium = equilibrium) :
    shiftedUpdate F equilibrium 0 = 0 := by
  simp [shiftedUpdate, he]

theorem actual_shifted_recurrence_is_equivalent_to_the_original_recurrence
    {E : Type*} [AddCommGroup E] (F : E → E) (equilibrium : E)
    (state : ℕ → E) :
    (∀ n, state (n + 1) = F (state n)) ↔
      ∀ n, state (n + 1) - equilibrium =
        shiftedUpdate F equilibrium (state n - equilibrium) := by
  simp only [shiftedUpdate, sub_add_cancel, sub_left_inj]

theorem actual_every_shifted_fixed_point_corresponds_to_an_original_fixed_point
    {E : Type*} [AddCommGroup E] (F : E → E) (equilibrium coordinate : E) :
    Function.IsFixedPt (shiftedUpdate F equilibrium) coordinate ↔
      Function.IsFixedPt F (coordinate + equilibrium) := by
  simp only [Function.IsFixedPt, shiftedUpdate, sub_eq_iff_eq_add]

theorem actual_shifted_constraint_and_storage_preserve_the_original_objects
    {E : Type*} [AddCommGroup E] (original : Set E) (V : E → ℝ)
    (equilibrium state : E) :
    (state - equilibrium ∈ shiftedConstraint original equilibrium ↔ state ∈ original) ∧
      shiftedStorage V equilibrium (state - equilibrium) = V state := by
  simp [shiftedConstraint, shiftedStorage]

theorem actual_shifted_storage_decrement_is_exactly_the_original_decrement
    {E : Type*} [AddCommGroup E] (F : E → E) (V : E → ℝ)
    (equilibrium state : E) :
    shiftedStorage V equilibrium
        (shiftedUpdate F equilibrium (state - equilibrium)) -
      shiftedStorage V equilibrium (state - equilibrium) =
        V (F state) - V state := by
  simp [shiftedStorage, shiftedUpdate]

end SafeLearning.CompleteFoundationsEquilibriumShift
