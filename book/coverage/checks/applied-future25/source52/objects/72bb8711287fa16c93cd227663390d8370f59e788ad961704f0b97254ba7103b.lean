import Mathlib

open Filter

namespace SafeLearning.CompleteModulesNNScalarPractices22

noncomputable section

/-- The exact plant and affine controller of NN Easy 1. -/
def plant (x u : ℝ) : ℝ := x / 2 + u
def controller (x : ℝ) : ℝ := x / 4 + 1
def affineLoop (x : ℝ) : ℝ := plant x (controller x)

/-- Substitution derives the source closed loop rather than assuming it. -/
theorem actual_controller_composition (x : ℝ) :
    affineLoop x = (3 / 4 : ℝ) * x + 1 := by
  unfold affineLoop plant controller
  ring

/-- All equilibrium pairs of the actual plant and controller are exactly (4,2). -/
theorem actual_unique_equilibrium_pair (x u : ℝ) :
    (plant x u = x ∧ u = controller x) ↔ x = 4 ∧ u = 2 := by
  constructor
  · rintro ⟨hx, hu⟩
    unfold plant at hx
    unfold controller at hu
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [plant, controller]

/-- The translation about the derived equilibrium removes the affine term. -/
theorem actual_shifted_deviation_dynamics (x : ℝ) :
    affineLoop x - 4 = (3 / 4 : ℝ) * (x - 4) := by
  rw [actual_controller_composition]
  ring

/-- The unshifted origin really moves to one and is not an equilibrium. -/
theorem actual_unshifted_origin_is_not_an_equilibrium :
    affineLoop 0 = 1 ∧ affineLoop 0 ≠ 0 := by
  norm_num [actual_controller_composition]

/-- The exact map and energy of NN Easy 2. -/
def energyStep (x : ℝ) : ℝ := (4 / 5 : ℝ) * x
def energy (x : ℝ) : ℝ := 2 * x ^ 2
def energyOrbit (x : ℝ) (n : ℕ) : ℝ := (energyStep^[n]) x

/-- The state multiplier is squared in the energy and its difference. -/
theorem actual_next_energy_and_lyapunov_difference (x : ℝ) :
    energy (energyStep x) = (32 / 25 : ℝ) * x ^ 2 ∧
    energy (energyStep x) - energy x = -(18 / 25 : ℝ) * x ^ 2 := by
  unfold energy energyStep
  constructor <;> ring

/-- The energy is nonnegative and the difference is strictly negative away from zero. -/
theorem actual_nonnegative_energy_and_strict_decrease (x : ℝ) (hx : x ≠ 0) :
    0 ≤ energy x ∧ energy (energyStep x) < energy x := by
  have hs : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  unfold energy energyStep
  constructor <;> nlinarith

/-- Every displayed value in the source one-step example is exact rational arithmetic. -/
theorem actual_literal_initial_two_values :
    energy 2 = 8 ∧ energyStep 2 = 8 / 5 ∧
    energy (energyStep 2) = 128 / 25 ∧
    energy 2 - energy (energyStep 2) = 72 / 25 := by
  norm_num [energy, energyStep]

/-- The actual recurrence has the geometric orbit from every real initial state. -/
theorem actual_all_iterates (x : ℝ) (n : ℕ) :
    energyOrbit x n = (4 / 5 : ℝ) ^ n * x := by
  unfold energyOrbit
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold energyStep
    rw [pow_succ]
    ring

/-- Convergence is derived for the actual trajectory, for every initial value. -/
theorem actual_every_initial_trajectory_converges (x : ℝ) :
    Tendsto (energyOrbit x) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (4 / 5 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq : energyOrbit x = fun n => (4 / 5 : ℝ) ^ n * x :=
    funext (actual_all_iterates x)
  rw [heq]
  simpa only [zero_mul] using h.mul_const x

end

end SafeLearning.CompleteModulesNNScalarPractices22
