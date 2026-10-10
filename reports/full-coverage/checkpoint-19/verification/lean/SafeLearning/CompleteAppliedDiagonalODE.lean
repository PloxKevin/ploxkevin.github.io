import SafeLearning.CompleteAppliedScalarODEBridges

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDiagonalODE
open Set Filter Matrix
open scoped Topology BigOperators
open SafeLearning.CompleteAppliedScalarODE
open SafeLearning.CompleteAppliedScalarODEBridges

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a, b]
def dynamics : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -2]
def trajectory (initial : E) (t : ℝ) : E :=
  point (solution (-1) (initial 0) t) (solution (-2) (initial 1) t)

theorem actual_euclidean_norm_square (v : E) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq v

theorem actual_diagonal_matrix_action (v : E) :
    dynamics.mulVec (WithLp.ofLp v) = ![-v 0, -2 * v 1] := by
  ext i
  fin_cases i <;> simp [dynamics, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem actual_diagonal_trajectory_initial (initial : E) : trajectory initial 0 = initial := by
  ext i
  fin_cases i <;> simp [trajectory, point, solution]

theorem actual_diagonal_trajectory_derivative (initial : E) (t : ℝ) :
    HasDerivAt (trajectory initial)
      (point (-trajectory initial t 0) (-2 * trajectory initial t 1)) t := by
  have hp : HasDerivAt
      (fun s => ![solution (-1) (initial 0) s, solution (-2) (initial 1) s])
      ![-solution (-1) (initial 0) t, -2 * solution (-2) (initial 1) t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using actual_linear_solution_ODE (-1) (initial 0) t
    · simpa using actual_linear_solution_ODE (-2) (initial 1) t
  convert (PiLp.hasFDerivAt_toLp (p := 2)
    ![solution (-1) (initial 0) t, solution (-2) (initial 1) t]).comp_hasDerivAt t hp using 1 <;>
    (try ext i) <;> simp [trajectory, point]

theorem actual_diagonal_trajectory_norm_decay (initial : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖trajectory initial t‖ ^ 2 ≤ ‖initial‖ ^ 2 * Real.exp (-2 * t) ∧
    ‖trajectory initial t‖ ≤ ‖initial‖ * Real.exp (-t) := by
  have he : Real.exp (-4 * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by linarith)
  have hs (a r : ℝ) : (solution r a t) ^ 2 = a ^ 2 * Real.exp (2 * r * t) := by
    rw [solution, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hsq : ‖trajectory initial t‖ ^ 2 ≤ ‖initial‖ ^ 2 * Real.exp (-2 * t) := by
    rw [actual_euclidean_norm_square, actual_euclidean_norm_square]
    simp only [trajectory, point, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hs, hs]
    norm_num
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (initial 1))
    norm_num at hh
    nlinarith
  refine ⟨hsq, ?_⟩
  have hexp : (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hn : 0 ≤ ‖initial‖ * Real.exp (-t) := by positivity
  nlinarith [norm_nonneg (trajectory initial t), hexp]

theorem actual_source_trajectory_and_bound (t : ℝ) (ht : 0 ≤ t) :
    trajectory (point 3 4) t = point (3 * Real.exp (-t)) (4 * Real.exp (-2 * t)) ∧
    ‖trajectory (point 3 4) t‖ ^ 2 = 9 * Real.exp (-2 * t) + 16 * Real.exp (-4 * t) ∧
    ‖trajectory (point 3 4) t‖ ≤ 5 * Real.exp (-t) := by
  have he : trajectory (point 3 4) t =
      point (3 * Real.exp (-t)) (4 * Real.exp (-2 * t)) := by
    ext i
    fin_cases i <;> simp [trajectory, point, solution]
  have hs : ‖point (3 : ℝ) 4‖ = 5 := by
    have hn : ‖point (3 : ℝ) 4‖ ^ 2 = 25 := by
      rw [actual_euclidean_norm_square]
      norm_num [point]
    nlinarith [norm_nonneg (point (3 : ℝ) 4)]
  refine ⟨he, ?_, ?_⟩
  · rw [he, actual_euclidean_norm_square]
    change (3 * Real.exp (-t)) ^ 2 + (4 * Real.exp (-2 * t)) ^ 2 = _
    have h2 : (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h4 : (Real.exp (-2 * t)) ^ 2 = Real.exp (-4 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, mul_pow, h2, h4]
    ring
  · simpa [hs] using (actual_diagonal_trajectory_norm_decay (point 3 4) t ht).2

theorem actual_matrix_Lyapunov_identity :
    dynamics.transpose * (1 : Matrix (Fin 2) (Fin 2) ℝ) + 1 * dynamics =
      !![-2, 0; 0, -4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [dynamics, Matrix.transpose_apply]

theorem actual_quadratic_decrement_bound (v : E) :
    -2 * (v 0) ^ 2 - 4 * (v 1) ^ 2 ≤ -2 * ‖v‖ ^ 2 ∧
    (v ≠ 0 → -2 * (v 0) ^ 2 - 4 * (v 1) ^ 2 < 0) := by
  rw [actual_euclidean_norm_square]
  constructor
  · nlinarith [sq_nonneg (v 1)]
  · intro hv
    have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    rw [actual_euclidean_norm_square] at hn
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

end SafeLearning.CompleteAppliedDiagonalODE
