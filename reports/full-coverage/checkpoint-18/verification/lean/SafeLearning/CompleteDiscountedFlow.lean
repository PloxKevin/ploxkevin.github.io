import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteDiscountedFlow

def transition (_ : Fin 2) : Fin 2 := 1
def trajectory (n : ℕ) : Fin 2 := if n = 0 then 0 else 1

theorem actual_trajectory (n : ℕ) :
    trajectory 0 = 0 ∧ trajectory (n + 1) = transition (trajectory n) := by
  simp [trajectory, transition]

def occupancy (s : Fin 2) : ℝ :=
  (1 / 2) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n * (if trajectory n = s then 1 else 0)

theorem initial_state_occupancy : occupancy 0 = 1 / 2 := by
  unfold occupancy
  rw [tsum_eq_single 0]
  · norm_num [trajectory]
  · intro n hn
    simp [trajectory, hn]

theorem successor_visitation_summable :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  simpa only [pow_succ] using
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_right (1 / 2)

theorem geometric_tail : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
  simp only [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by norm_num)]
  norm_num

theorem absorbing_state_occupancy : occupancy 1 = 1 / 2 := by
  have hs : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ (n + 1) * (if trajectory (n + 1) = 1 then 1 else 0)) := by
    simpa [trajectory] using successor_visitation_summable
  have he := tsum_eq_zero_add' (f := fun n : ℕ =>
    (1 / 2 : ℝ) ^ n * (if trajectory n = 1 then 1 else 0)) hs
  have ht : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
      (if trajectory (n + 1) = 1 then 1 else 0)) = 1 := by
    calc
      _ = ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) := by
        apply tsum_congr
        intro n
        simp [trajectory]
      _ = 1 := geometric_tail
  unfold occupancy
  rw [he, ht]
  norm_num [trajectory]

theorem normalized_occupancy_sum : occupancy 0 + occupancy 1 = 1 := by
  rw [initial_state_occupancy, absorbing_state_occupancy]
  norm_num

def initialLaw (s : Fin 2) : ℝ := if s = 0 then 1 else 0
def kernel (origin target : Fin 2) : ℝ := if transition origin = target then 1 else 0

theorem actual_flow_equations (s : Fin 2) :
    occupancy s = (1 / 2) * initialLaw s +
      (1 / 2) * ∑ t : Fin 2, occupancy t * kernel t s := by
  fin_cases s <;>
    norm_num [initialLaw, kernel, transition, Fin.sum_univ_succ,
      initial_state_occupancy, absorbing_state_occupancy]

theorem flow_coordinates_unique (r0 r1 : ℝ)
    (h0 : r0 = 1 / 2) (h1 : r1 = (1 / 2) * (r0 + r1)) :
    r0 = occupancy 0 ∧ r1 = occupancy 1 := by
  rw [initial_state_occupancy, absorbing_state_occupancy]
  constructor <;> linarith

def reward (s : Fin 2) : ℝ := (![0, 2] : Fin 2 → ℝ) s
def actualReturn : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ n * reward (trajectory n)

theorem return_successor_term (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * reward (trajectory (n + 1)) = (1 / 2 : ℝ) ^ n := by
  simp [trajectory, reward, pow_succ]

theorem actual_infinite_return : actualReturn = 2 := by
  have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * reward (trajectory (n + 1))) := by
    simp_rw [return_successor_term]
    exact summable_geometric_of_abs_lt_one (by norm_num)
  have he := tsum_eq_zero_add' (f := fun n : ℕ =>
    (1 / 2 : ℝ) ^ n * reward (trajectory n)) hs
  unfold actualReturn
  rw [he]
  simp_rw [return_successor_term]
  rw [tsum_geometric_of_abs_lt_one (by norm_num)]
  norm_num [trajectory, reward]

theorem normalized_reward_return_identity :
    (∑ s : Fin 2, occupancy s * reward s) = 1 ∧
      (∑ s : Fin 2, occupancy s * reward s) / (1 - (1 / 2 : ℝ)) = actualReturn := by
  rw [actual_infinite_return]
  norm_num [Fin.sum_univ_succ, reward, initial_state_occupancy, absorbing_state_occupancy]

end SafeLearning.CompleteDiscountedFlow
