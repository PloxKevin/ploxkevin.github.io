import SafeLearning.CompleteAppliedDiagonalODE

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDiagonalCertificates
open Set Filter Matrix
open scoped Topology BigOperators
open SafeLearning.CompleteAppliedScalarODEBridges
open SafeLearning.CompleteAppliedDiagonalODE

theorem actual_identity_storage_and_positive_definiteness (v : E) :
    (WithLp.ofLp v) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ).mulVec (WithLp.ofLp v)) =
      ‖v‖ ^ 2 ∧ Matrix.PosDef (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨?_, Matrix.PosDef.one⟩
  simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_two]
  rw [actual_euclidean_norm_square]
  ring

theorem actual_negative_Lyapunov_matrix_is_positive_after_negation :
    Matrix.PosDef (- (!![-2, 0; 0, -4] : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have he : - (!![-2, 0; 0, -4] : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal ![2, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  rw [he]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem actual_coordinate_derivatives_from_vector_ODE
    (x : ℝ → E) (t : ℝ)
    (hd : HasDerivAt x (point (-x t 0) (-2 * x t 1)) t) :
    HasDerivAt (fun s => x s 0) (-x t 0) t ∧
      HasDerivAt (fun s => x s 1) (-2 * x t 1) t := by
  constructor
  · simpa [point, Function.comp_def] using
      (PiLp.hasFDerivAt_apply (p := 2) (x t) 0).comp_hasDerivAt t hd
  · simpa [point, Function.comp_def] using
      (PiLp.hasFDerivAt_apply (p := 2) (x t) 1).comp_hasDerivAt t hd

theorem actual_every_existing_diagonal_ODE_trajectory
    (x : ℝ → E)
    (hd : ∀ t ≥ 0, HasDerivAt x (point (-x t 0) (-2 * x t 1)) t) :
    ∀ t ≥ 0, x t = trajectory (x 0) t := by
  have h0 : ∀ t ≥ 0, HasDerivAt (fun s => x s 0) ((-1) * x t 0) t := by
    intro t ht
    simpa using (actual_coordinate_derivatives_from_vector_ODE x t (hd t ht)).1
  have h1 : ∀ t ≥ 0, HasDerivAt (fun s => x s 1) ((-2) * x t 1) t := by
    intro t ht
    simpa using (actual_coordinate_derivatives_from_vector_ODE x t (hd t ht)).2
  have he0 := actual_existing_linear_trajectory_equals_solution (fun t => x t 0)
    (-1) (x 0 0) rfl h0
  have he1 := actual_existing_linear_trajectory_equals_solution (fun t => x t 1)
    (-2) (x 0 1) rfl h1
  intro t ht
  ext i
  fin_cases i
  · simpa [trajectory, point] using he0 t ht
  · simpa [trajectory, point] using he1 t ht

theorem actual_norm_square_certificate_derivative
    (x : ℝ → E) (t : ℝ)
    (hd : HasDerivAt x (point (-x t 0) (-2 * x t 1)) t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2) (-2 * (x t 0) ^ 2 - 4 * (x t 1) ^ 2) t := by
  have hc := actual_coordinate_derivatives_from_vector_ODE x t hd
  have hs := (hc.1.pow 2).add (hc.2.pow 2)
  convert hs using 1
  · funext s
    exact actual_euclidean_norm_square (x s)
  · ring

theorem actual_all_diagonal_ODE_norm_decay
    (x : ℝ → E)
    (hd : ∀ t ≥ 0, HasDerivAt x (point (-x t 0) (-2 * x t 1)) t) :
    (∀ t ≥ 0, ‖x t‖ ^ 2 ≤ ‖x 0‖ ^ 2 * Real.exp (-2 * t) ∧
      ‖x t‖ ≤ ‖x 0‖ * Real.exp (-t)) ∧ Tendsto x atTop (𝓝 0) := by
  have he := actual_every_existing_diagonal_ODE_trajectory x hd
  have hb : ∀ t ≥ 0, ‖x t‖ ^ 2 ≤ ‖x 0‖ ^ 2 * Real.exp (-2 * t) ∧
      ‖x t‖ ≤ ‖x 0‖ * Real.exp (-t) := by
    intro t ht
    rw [he t ht]
    exact actual_diagonal_trajectory_norm_decay (x 0) t ht
  refine ⟨hb, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun t : ℝ => ‖x 0‖ * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ‖x 0‖
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (x t)) _ hg
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hb t ht).2

end SafeLearning.CompleteAppliedDiagonalCertificates
