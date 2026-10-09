import SafeLearning.CompleteProjectionCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace SafeLearning.CompleteProjectionDifferential

open SafeLearning.CompleteWeightedProjection SafeLearning.CompleteProjectionCharacterization

theorem quadratic_line_formula {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (nominal u v : ι → ℝ) (t : ℝ) :
    objective H nominal (u + t • v) =
      ((1 / 2) * energy H v) * t ^ 2 + (v ⬝ᵥ (H *ᵥ (u - nominal))) * t +
        objective H nominal u := by
  have he : u + t • v - nominal = t • v + (u - nominal) := by abel
  unfold objective
  rw [he, energy_expansion H hH]
  simp only [energy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem objective_line_derivative {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (nominal u v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => objective H nominal (u + t • v))
      (v ⬝ᵥ (H *ᵥ (u - nominal))) 0 := by
  have hp := ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul ((1 / 2) * energy H v)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (v ⬝ᵥ (H *ᵥ (u - nominal))))).add_const
      (objective H nominal u)
  convert hp using 1
  · funext t
    exact quadratic_line_formula H hH nominal u v t
  · simp

theorem objective_differentiable {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (nominal u : ι → ℝ) :
    DifferentiableAt ℝ (objective H nominal) u := by
  unfold objective energy Matrix.mulVec dotProduct
  fun_prop

/-- The actual Fréchet derivative is the dot product with H(u-u_nom). -/
theorem actual_objective_gradient {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (nominal u v : ι → ℝ) :
    (fderiv ℝ (objective H nominal) u) v = (H *ᵥ (u - nominal)) ⬝ᵥ v := by
  have hl : HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u using 1 <;> simp
  have hc := (objective_differentiable H nominal u).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hl (by simp)
  simpa only [dotProduct_comm] using hc.unique (objective_line_derivative H hH nominal u v)

theorem identity_example_multiplier :
    multiplier (1 : Matrix (Fin 2) (Fin 2) ℝ) (-3) ![1, 1] ![1, 1] = 1 / 2 := by
  norm_num [multiplier, dotProduct, Fin.sum_univ_succ]

theorem identity_example_solution :
    solution (1 : Matrix (Fin 2) (Fin 2) ℝ) (-3) ![1, 1] ![1, 1] = ![3 / 2, 3 / 2] := by
  simp only [solution, identity_example_multiplier, inv_one, one_mulVec]
  ext i
  fin_cases i <;> norm_num

theorem actual_numeric_comparison :
    solution exampleWeight (-3) ![1, 1] ![1, 1] = ![9 / 5, 6 / 5] ∧
    solution (1 : Matrix (Fin 2) (Fin 2) ℝ) (-3) ![1, 1] ![1, 1] = ![3 / 2, 3 / 2] ∧
    multiplier exampleWeight (-3) ![1, 1] ![1, 1] = 4 / 5 := by
  refine ⟨example_solution, identity_example_solution, ?_⟩
  simp only [multiplier, example_inverse_direction]
  norm_num [dotProduct, Fin.sum_univ_succ]

end SafeLearning.CompleteProjectionDifferential
