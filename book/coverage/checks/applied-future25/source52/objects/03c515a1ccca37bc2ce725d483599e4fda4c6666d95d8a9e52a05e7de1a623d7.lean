import Mathlib

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace SafeLearning.CompletePolicyTrustStep

def metric : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 4]
def gradient : Fin 2 → ℝ := ![1, 2]
def step : Fin 2 → ℝ := ![1 / Real.sqrt 2, 1 / (2 * Real.sqrt 2)]
def quadratic (x : Fin 2 → ℝ) : ℝ := dotProduct x (metric *ᵥ x)
def objective (x : Fin 2 → ℝ) : ℝ := dotProduct gradient x

theorem genuine_matrix_inverse : metric⁻¹ = !![1, 0; 0, 1 / 4] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [metric, Matrix.mul_apply, Fin.sum_univ_two]

theorem genuine_inverse_gradient : metric⁻¹ *ᵥ gradient = ![1, 1 / 2] := by
  rw [genuine_matrix_inverse]
  ext i
  fin_cases i <;> norm_num [gradient, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem genuine_inverse_gradient_inner :
    dotProduct gradient (metric⁻¹ *ᵥ gradient) = 2 := by
  rw [genuine_inverse_gradient]
  norm_num [gradient, dotProduct, Fin.sum_univ_two]

theorem actual_matrix_objective_and_constraint (x : Fin 2 → ℝ) :
    quadratic x = x 0 ^ 2 + 4 * x 1 ^ 2 ∧ objective x = x 0 + 2 * x 1 := by
  simp [quadratic, objective, metric, gradient, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem actual_TRPO_formula (i : Fin 2) :
    step i = Real.sqrt (2 * (1 / 2) / dotProduct gradient (metric⁻¹ *ᵥ gradient)) *
      (metric⁻¹ *ᵥ gradient) i := by
  rw [genuine_inverse_gradient_inner, genuine_inverse_gradient]
  fin_cases i <;> simp [step, Real.sqrt_div] <;> ring

theorem actual_step_boundary_and_reward : quadratic step = 1 ∧
    (1 / 2) * quadratic step = 1 / 2 ∧ objective step = Real.sqrt 2 := by
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨hq, ho⟩ := actual_matrix_objective_and_constraint step
  have hb : quadratic step = 1 := by
    rw [hq]
    simp only [step, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    nlinarith
  refine ⟨hb, by rw [hb]; norm_num, ?_⟩
  rw [ho]
  simp only [step, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  nlinarith

theorem actual_metric_Cauchy_Schwarz (x : Fin 2 → ℝ) :
    objective x ^ 2 ≤
      dotProduct gradient (metric⁻¹ *ᵥ gradient) * quadratic x := by
  rw [genuine_inverse_gradient_inner, (actual_matrix_objective_and_constraint x).1,
    (actual_matrix_objective_and_constraint x).2]
  nlinarith [sq_nonneg (x 0 - 2 * x 1)]

theorem genuine_global_trust_region_optimum (x : Fin 2 → ℝ)
    (hx : (1 / 2) * quadratic x ≤ 1 / 2) : objective x ≤ objective step := by
  have h := actual_metric_Cauchy_Schwarz x
  rw [genuine_inverse_gradient_inner] at h
  rw [actual_step_boundary_and_reward.2.2]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hq : quadratic x ≤ 1 := by linarith
  nlinarith

end SafeLearning.CompletePolicyTrustStep
