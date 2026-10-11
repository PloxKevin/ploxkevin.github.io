import SafeLearning.CompleteAppliedScalarODE

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedScalarConsequences
open SafeLearning.CompleteAppliedScalarTrajectories SafeLearning.CompleteAppliedScalarODE

theorem actual_comparison_ODE_solution_initial_and_derivative :
    (4 * Real.exp (-3 * (0 : ℝ))) = 4 ∧
      ∀ t : ℝ, HasDerivAt (fun s => 4 * Real.exp (-3 * s))
        (-3 * (4 * Real.exp (-3 * t))) t := by
  refine ⟨by norm_num, ?_⟩
  intro t
  change HasDerivAt (solution (-3) 4) (-3 * solution (-3) 4 t) t
  exact actual_linear_solution_ODE (-3) 4 t

theorem actual_comparison_sublevel_time_iff (t : ℝ) :
    4 * Real.exp (-3 * t) ≤ 1 / 5 ↔ Real.log (20 : ℝ) / 3 ≤ t := by
  have he : Real.exp (-Real.log (20 : ℝ)) = 1 / 20 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 20)]
    norm_num
  constructor
  · intro h
    have hs : Real.exp (-3 * t) ≤ Real.exp (-Real.log (20 : ℝ)) := by
      rw [he]
      linarith
    have hl := Real.exp_le_exp.mp hs
    linarith
  · intro h
    have hs : Real.exp (-3 * t) ≤ Real.exp (-Real.log (20 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [he] at hs
    linarith

theorem actual_source_sublevel_time_four_decimal_rounding :
    |Real.log (20 : ℝ) / 3 - (9986 / 10000 : ℝ)| < 1 / 20000 := by
  have h := actual_sublevel_entry_time_rounding
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

theorem actual_source_barrier_gradient (x : ℝ) :
    HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
  simpa using (hasDerivAt_id x).const_sub 1

theorem actual_source_barrier_derivative_along_trajectory
    (x u : ℝ → ℝ) (t : ℝ) (hx : HasDerivAt x (u t) t) :
    HasDerivAt (fun s => 1 - x s) (-u t) t := by
  simpa using hx.const_sub 1

end SafeLearning.CompleteAppliedScalarConsequences
