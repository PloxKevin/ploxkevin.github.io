import SafeLearning.CompleteAppliedCubicSublevelConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SafeLearning.CompleteAppliedCubicSublevelSource
open CompleteAppliedCubicSublevel CompleteAppliedCubicSublevelConsequences

theorem actual_along_trajectory_storage_chain_rule_and_sublevel_bound
    (x : ℝ → ℝ) (time c : ℝ) (hd : HasDerivAt x (field (x time)) time)
    (hc : storage (x time) ≤ c) :
    HasDerivAt (fun t => storage (x t)) (-2 * storage (x time) * (1 - storage (x time))) time ∧
      -2 * storage (x time) * (1 - storage (x time)) ≤
        -2 * (1 - c) * storage (x time) := by
  have h := (actual_storage_derivative_and_sublevel_decrease (x time) c hc).2
  constructor
  · have hs := ((actual_storage_derivative_and_sublevel_decrease (x time) c hc).1).comp time hd
    convert hs using 1 <;> first | rfl | (dsimp [storage, field]; ring)
  · dsimp [storage] at h ⊢
    nlinarith [h.1, h.2]

theorem actual_any_finite_ac_solution_in_the_closed_unit_sublevel_has_a_global_continuation
    (x : ℝ → ℝ) (initial horizon : ℝ) (hi : storage initial ≤ 1) (hT : 0 ≤ horizon)
    (hc : AbsolutelyContinuousOnInterval x 0 horizon) (hx0 : x 0 = initial)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time) :
    ∃ extension : ℝ → ℝ,
      EqOn x extension (Icc 0 horizon) ∧ extension 0 = initial ∧
      (∀ bound : ℝ, 0 ≤ bound → AbsolutelyContinuousOnInterval extension 0 bound) ∧
      (∀ time : ℝ, 0 ≤ time → HasDerivAt extension (field (extension time)) time) ∧
      (∀ time : ℝ, 0 ≤ time → |extension time| ≤ |initial|) := by
  have hs := actual_every_initial_in_the_closed_unit_sublevel_has_a_global_solution initial hi
  exact ⟨actualSolution initial,
    actual_every_closed_unit_sublevel_ac_trajectory_equals_the_global_solution
      x initial horizon hi hT hc hx0 hd,
    hs.1, hs.2.1, hs.2.2,
    fun time ht => actual_forward_solution_magnitude_does_not_exceed_initial_magnitude initial time hi ht⟩

theorem actual_global_solution_has_a_finite_continuous_value_at_every_forward_endpoint
    (initial endpoint : ℝ) (hi : storage initial ≤ 1) (hendpoint : 0 ≤ endpoint) :
    Tendsto (actualSolution initial) (𝓝[<] endpoint) (𝓝 (actualSolution initial endpoint)) := by
  exact ((actual_every_initial_in_the_closed_unit_sublevel_has_a_global_solution initial hi).2.2
    endpoint hendpoint).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end SafeLearning.CompleteAppliedCubicSublevelSource
