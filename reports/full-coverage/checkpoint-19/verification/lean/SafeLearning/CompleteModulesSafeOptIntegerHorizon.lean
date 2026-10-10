import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SafeLearning.CompleteModulesSafeOptIntegerHorizon

/-- The literal floor-window budget is exactly an integer ceiling condition
on the horizon, with positive epsilon and a positive number of windows. -/
theorem actual_floor_window_width_budget_is_equivalent_to_the_ceiling_horizon_condition
    (horizon windows : ℕ) (hwindows : 0 < windows) (budget epsilon : ℝ) (hepsilon : 0 < epsilon) :
    budget ≤ ((horizon / windows : ℕ) : ℝ) * epsilon ^ 2 ↔
      windows * ⌈budget / epsilon ^ 2⌉₊ ≤ horizon := by
  rw [← div_le_iff₀ (pow_pos hepsilon 2),← Nat.ceil_le,Nat.le_div_iff_mul_le hwindows]
  rw [Nat.mul_comm]

/-- Cardinality-plus-one times the larger of one and the required integer
ceiling guarantees a positive allocated window and its actual width budget. -/
theorem actual_rounded_integer_horizon_guarantees_a_positive_window_and_its_width_budget
    (horizon windows : ℕ) (hwindows : 0 < windows) (budget epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hrounded : windows * max 1 ⌈budget / epsilon ^ 2⌉₊ ≤ horizon) :
    0 < horizon / windows ∧ budget ≤ ((horizon / windows : ℕ) : ℝ) * epsilon ^ 2 := by
  have hallocated : max 1 ⌈budget / epsilon ^ 2⌉₊ ≤ horizon / windows :=
    (Nat.le_div_iff_mul_le hwindows).mpr (by simpa only [Nat.mul_comm] using hrounded)
  have hone : 1 ≤ horizon / windows := (le_max_left _ _).trans hallocated
  refine ⟨by omega,?_⟩
  apply (actual_floor_window_width_budget_is_equivalent_to_the_ceiling_horizon_condition
    horizon windows hwindows budget epsilon hepsilon).mpr
  exact (Nat.mul_le_mul_left windows (le_max_right 1 ⌈budget / epsilon ^ 2⌉₊)).trans hrounded

/-- A real quotient condition alone need not imply the floor-window condition.
This is only an arithmetic rounding witness, not a SafeOpt counterexample. -/
theorem actual_real_quotient_budget_does_not_by_itself_imply_the_floor_window_budget :
    (3 / 2 : ℝ) ≤ (3 : ℝ) / 2 ∧ ¬ (3 / 2 : ℝ) ≤ ((3 / 2 : ℕ) : ℝ) := by
  norm_num

end SafeLearning.CompleteModulesSafeOptIntegerHorizon
