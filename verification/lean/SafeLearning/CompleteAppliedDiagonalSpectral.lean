import SafeLearning.CompleteAppliedDiagonalCertificates

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDiagonalSpectral
open Set Filter Matrix
open scoped Topology BigOperators
open SafeLearning.CompleteAppliedDiagonalODE
open SafeLearning.CompleteAppliedDiagonalCertificates

def complexDynamics : Matrix (Fin 2) (Fin 2) ℂ := dynamics.map Complex.ofReal

theorem actual_complexified_matrix_is_the_source_diagonal :
    complexDynamics = Matrix.diagonal ![-1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [complexDynamics, dynamics, Matrix.diagonal]

theorem actual_complex_spectrum_iff (z : ℂ) :
    z ∈ spectrum ℂ complexDynamics ↔ z = -1 ∨ z = -2 := by
  rw [actual_complexified_matrix_is_the_source_diagonal, spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa using hi.symm)
    · exact Or.inr (by simpa using hi.symm)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem actual_complex_eigenvalues_exactly_minus_one_and_minus_two (z : ℂ) :
    Module.End.HasEigenvalue complexDynamics.toLin' z ↔ z = -1 ∨ z = -2 := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  exact actual_complex_spectrum_iff z

theorem actual_all_complex_eigenvalues_have_negative_real_part (z : ℂ)
    (hz : Module.End.HasEigenvalue complexDynamics.toLin' z) : z.re < 0 := by
  rcases (actual_complex_eigenvalues_exactly_minus_one_and_minus_two z).mp hz with rfl | rfl
  · norm_num
  · norm_num

theorem actual_source_Lyapunov_matrix_is_twice_dynamics :
    dynamics.transpose * (1 : Matrix (Fin 2) (Fin 2) ℝ) + 1 * dynamics =
      (2 : ℝ) • dynamics := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [dynamics, Matrix.transpose_apply]

theorem actual_quadratic_matrix_form_is_the_source_decrement (v : E) :
    WithLp.ofLp v ⬝ᵥ
      ((dynamics.transpose * (1 : Matrix (Fin 2) (Fin 2) ℝ) + 1 * dynamics).mulVec
        (WithLp.ofLp v)) = -2 * (v 0) ^ 2 - 4 * (v 1) ^ 2 := by
  rw [actual_matrix_Lyapunov_identity]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem actual_matrix_ODE_trajectory_semantics
    (x : ℝ → E)
    (hd : ∀ t ≥ 0, HasDerivAt x (WithLp.toLp 2 (dynamics.mulVec (WithLp.ofLp (x t)))) t) :
    (∀ t ≥ 0, x t = trajectory (x 0) t) ∧
      (∀ t ≥ 0, ‖x t‖ ^ 2 ≤ ‖x 0‖ ^ 2 * Real.exp (-2 * t) ∧
        ‖x t‖ ≤ ‖x 0‖ * Real.exp (-t)) ∧ Tendsto x atTop (𝓝 0) := by
  have hp : ∀ t ≥ 0, HasDerivAt x (point (-x t 0) (-2 * x t 1)) t := by
    intro t ht
    simpa only [actual_diagonal_matrix_action, point] using hd t ht
  exact ⟨actual_every_existing_diagonal_ODE_trajectory x hp,
    actual_all_diagonal_ODE_norm_decay x hp⟩

theorem actual_matrix_ODE_certificate_derivative
    (x : ℝ → E) (t : ℝ)
    (hd : HasDerivAt x (WithLp.toLp 2 (dynamics.mulVec (WithLp.ofLp (x t)))) t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2)
      (WithLp.ofLp (x t) ⬝ᵥ
        ((dynamics.transpose * (1 : Matrix (Fin 2) (Fin 2) ℝ) + 1 * dynamics).mulVec
          (WithLp.ofLp (x t)))) t := by
  rw [actual_quadratic_matrix_form_is_the_source_decrement]
  apply actual_norm_square_certificate_derivative
  simpa only [actual_diagonal_matrix_action, point] using hd

end SafeLearning.CompleteAppliedDiagonalSpectral
