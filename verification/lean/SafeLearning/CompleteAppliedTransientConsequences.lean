import SafeLearning.CompleteAppliedTransientAmplification

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedTransientConsequences
open CompleteAppliedTransientAmplification

theorem actual_euclidean_and_lyapunov_norm_bounds (x : E) :
    ‖x‖≤actualLyapunovNorm x ∧ actualLyapunovNorm x≤41*‖x‖ := by
  have hsq : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have h0 : |x 0|≤‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x (0:Fin 2)
  have h1 : |x 1|≤‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x (1:Fin 2)
  change ‖x‖≤|x 0|+40*|x 1| ∧ |x 0|+40*|x 1|≤41*‖x‖
  have hl : ‖x‖≤|x 0|+|x 1| := by
    nlinarith [sq_abs (x 0),sq_abs (x 1),norm_nonneg x,
      abs_nonneg (x 0),abs_nonneg (x 1),mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]
  constructor <;> linarith [abs_nonneg (x 1)]

theorem actual_lyapunov_norm_has_uniform_all_time_bound (initial : E) (n : ℕ) :
    actualLyapunovNorm (trajectory initial n)≤actualLyapunovNorm initial := by
  induction n with
  | zero => rw [(actual_initial_and_recurrence initial).1]
  | succ n ih =>
    rw [(actual_initial_and_recurrence initial).2]
    have h := actual_lyapunov_norm_contracts_every_step (trajectory initial n)
    have hn : 0≤actualLyapunovNorm (trajectory initial n) := by
      change 0≤|trajectory initial n 0|+40*|trajectory initial n 1|
      positivity
    linarith

theorem actual_uniform_euclidean_amplification_is_bounded_for_every_initial
    (initial : E) (n : ℕ) : ‖trajectory initial n‖≤41*‖initial‖ := by
  exact ((actual_euclidean_and_lyapunov_norm_bounds (trajectory initial n)).1.trans
    (actual_lyapunov_norm_has_uniform_all_time_bound initial n)).trans
    (actual_euclidean_and_lyapunov_norm_bounds initial).2

theorem actual_origin_is_lyapunov_stable :
    ∀ε:ℝ,0<ε→∃δ:ℝ,0<δ∧∀initial:E,‖initial‖<δ→∀n:ℕ,
      ‖trajectory initial n‖<ε := by
  intro ε hε
  refine ⟨ε/41,by positivity,?_⟩
  intro initial hi n
  have h := actual_uniform_euclidean_amplification_is_bounded_for_every_initial initial n
  linarith

theorem actual_every_existing_recurrence_is_stable_and_convergent
    (initial : E) (x : ℕ→E) (h0 : x 0=initial) (hn : ∀n,x (n+1)=step (x n)) :
    (∀n,‖x n‖≤41*‖initial‖) ∧ Tendsto x atTop (𝓝 0) := by
  have he := actual_every_recurrence_is_this_trajectory initial x h0 hn
  constructor
  · intro n;rw [he n];exact actual_uniform_euclidean_amplification_is_bounded_for_every_initial initial n
  · have hf : x=trajectory initial := funext he
    rw [hf]
    exact actual_every_initial_trajectory_tends_to_zero initial

theorem actual_source_displayed_transient_norm_is_the_true_square_root :
    ‖trajectory (point 0 1) 1‖=Real.sqrt (401/4) := by
  have hs := actual_source_euclidean_transient_and_decimal.2.2.1
  have he := congrArg Real.sqrt hs
  simpa [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] using he

def complexDynamics : Matrix (Fin 2) (Fin 2) ℂ := dynamics.map Complex.ofReal

theorem actual_full_complex_spectrum_is_the_single_stable_eigenvalue (z : ℂ) :
    z∈spectrum ℂ complexDynamics ↔ z=(1/2:ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_fin_two]
  have he : Polynomial.eval z
      (Polynomial.X^2-Polynomial.C (Matrix.trace complexDynamics)*Polynomial.X+
        Polynomial.C (Matrix.det complexDynamics))=(z-1/2)^2 := by
    norm_num [complexDynamics,dynamics,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
    ring
  change Polynomial.eval z _=0 ↔ _
  rw [he]
  simp [sq_eq_zero_iff,sub_eq_zero]

end SafeLearning.CompleteAppliedTransientConsequences
