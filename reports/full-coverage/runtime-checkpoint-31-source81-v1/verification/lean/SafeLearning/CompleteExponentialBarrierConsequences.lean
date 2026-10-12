import SafeLearning.CompleteExponentialBarrier

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace SafeLearning.CompleteExponentialBarrierConsequences
open CompleteExponentialBarrier

def inputMatrix : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
def gainRow (k1 k2 : ℝ) : Matrix (Fin 1) (Fin 2) ℝ := !![k1, k2]

theorem actual_F_minus_GK (k1 k2 : ℝ) :
    companion - inputMatrix * gainRow k1 k2 = closedMatrix k1 k2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, inputMatrix, gainRow, closedMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem actual_gain_row_evaluation (k1 k2 p v : ℝ) :
    (gainRow k1 k2 *ᵥ eta p v) 0 = k1 * (1 - p) - k2 * v := by
  simp [gainRow, eta, barrier, mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem actual_source_G_and_mu_dynamics (p v u : ℝ) :
    companion *ᵥ eta p v + inputMatrix *ᵥ (![-u] : Fin 1 → ℝ) =
      (![-v, -u] : Fin 2 → ℝ) := by
  ext i
  fin_cases i <;> simp [companion, eta, inputMatrix, mulVec, dotProduct, Fin.sum_univ_succ]

theorem all_initial_margin_cases (margin rate pole : ℝ) (hm : 0 ≤ margin) :
    0 ≤ rate + pole * margin ↔
      if margin = 0 then 0 ≤ rate else -rate / margin ≤ pole := by
  by_cases hzero : margin = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    exact correct_positive_margin_ratio margin rate pole (lt_of_le_of_ne hm (Ne.symm hzero))

theorem actual_zero_auxiliary_requires_rate_condition (p2 : ℝ) :
    auxiliary 1 0 1 = 0 ∧ auxiliaryRate 1 1 0 = -1 ∧
      ¬ 0 ≤ auxiliaryRate 1 1 0 + p2 * auxiliary 1 0 1 := by
  norm_num [auxiliary, auxiliaryRate, barrier]

theorem totalized_zero_denominator_does_not_test_initial_safety (p2 : ℝ)
    (hp2 : 0 < p2) :
    -auxiliaryRate 1 1 0 / auxiliary 1 0 1 ≤ p2 ∧
      ¬ 0 ≤ auxiliaryRate 1 1 0 + p2 * auxiliary 1 0 1 := by
  norm_num [auxiliary, auxiliaryRate, barrier]
  exact hp2.le

theorem actual_zero_auxiliary_feasible_initial_input (p2 : ℝ) :
    auxiliary 1 0 1 = 0 ∧
      0 < auxiliaryRate 1 1 (-2) + p2 * auxiliary 1 0 1 ∧
      (-2 : ℝ) ≤ 1 * p2 - (1 + p2) := by
  norm_num [auxiliary, auxiliaryRate, barrier]

end SafeLearning.CompleteExponentialBarrierConsequences
