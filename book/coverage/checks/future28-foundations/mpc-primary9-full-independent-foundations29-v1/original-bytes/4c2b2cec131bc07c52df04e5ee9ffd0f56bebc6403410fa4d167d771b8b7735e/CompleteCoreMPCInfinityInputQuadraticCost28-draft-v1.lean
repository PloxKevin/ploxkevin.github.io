import SafeLearning.CompleteCoreMPCHybridMatrixInfinityInput26

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteCoreMPCInfinityInputCost28
open SafeLearning.CompleteCoreMPCFiniteEntrySwitch26

/-- The physical input has the infinity norm used by the feedback certificate.
Its cost uses the same coordinates in the source Euclidean quadratic form,
exactly as in the selected terminal matrix convergence theorem. -/
def actualInputQuadratic {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin m → ℝ) : ℝ :=
  matrixQuadraticStorage R (WithLp.toLp 2 u)

theorem actual_input_cost_preserves_every_physical_coordinate
    {m : ℕ} (u : Fin m → ℝ) (i : Fin m) :
    (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m)) i = u i := by
  rfl

theorem actual_infinity_input_matrix_quadratic_is_continuous
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (actualInputQuadratic R) := by
  exact (actual_matrix_quadratic_storage_is_continuous R).comp
    (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin m => ℝ))

theorem actual_Q_R_stage_and_P_terminal_costs_are_continuous_in_the_physical_spaces
    {n m : ℕ} (Q P : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) × (Fin m → ℝ) =>
      matrixQuadraticStorage Q z.1 + actualInputQuadratic R z.2) ∧
    Continuous (matrixQuadraticStorage P) := by
  exact ⟨((actual_matrix_quadratic_storage_is_continuous Q).comp continuous_fst).add
    ((actual_infinity_input_matrix_quadratic_is_continuous R).comp continuous_snd),
    actual_matrix_quadratic_storage_is_continuous P⟩

theorem actual_positive_definite_input_matrix_has_nonnegative_physical_cost
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (u : Fin m → ℝ) : 0 ≤ actualInputQuadratic R u := by
  exact actual_positive_definite_matrix_has_nonnegative_quadratic_storage R hR _

end SafeLearning.CompleteCoreMPCInfinityInputCost28
