import SafeLearning.CompleteAppliedScalarODE

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedScalarODEBridges
open Set Filter
open scoped Topology
open SafeLearning.CompleteAppliedScalarODE

theorem actual_positive_rate_all_nonzero_magnitudes_grow
    (rate initial : ℝ) (hr : 0 < rate) (hi : initial ≠ 0) :
    Tendsto (fun t => |solution rate initial t|) atTop atTop := by
  have he := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr)
  have hm := he.const_mul_atTop (abs_pos.mpr hi)
  simpa only [solution, abs_mul, abs_of_pos (Real.exp_pos _), Function.comp_def,
    id_eq] using hm

theorem actual_feedback_all_nonzero_magnitudes_grow
    (k initial : ℝ) (hk : k < 2) (hi : initial ≠ 0) :
    Tendsto (fun t => |solution (2 - k) initial t|) atTop atTop :=
  actual_positive_rate_all_nonzero_magnitudes_grow (2 - k) initial (by linarith) hi

theorem actual_existing_linear_trajectory_equals_solution
    (x : ℝ → ℝ) (rate initial : ℝ)
    (hi : x 0 = initial)
    (hd : ∀ t ≥ 0, HasDerivAt x (rate * x t) t) :
    ∀ t ≥ 0, x t = solution rate initial t := by
  intro t ht
  have hc : ContinuousOn x (Icc 0 t) := by
    intro s hs
    exact (hd s hs.1).continuousAt.continuousWithinAt
  exact actual_linear_ODE_unique x rate initial t hc hi
    (fun s hs => hd s hs.1) t ⟨ht, le_rfl⟩

theorem actual_existing_linear_trajectory_converges
    (x : ℝ → ℝ) (rate initial : ℝ) (hr : rate < 0)
    (hi : x 0 = initial)
    (hd : ∀ t ≥ 0, HasDerivAt x (rate * x t) t) :
    Tendsto x atTop (𝓝 0) := by
  have he := actual_existing_linear_trajectory_equals_solution x rate initial hi hd
  apply (((actual_linear_all_initial_attraction_iff rate).mpr hr) initial).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (he t ht).symm

theorem actual_source_quadratic_gradient (x : ℝ) :
    HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> (try ext z) <;> norm_num

end SafeLearning.CompleteAppliedScalarODEBridges
