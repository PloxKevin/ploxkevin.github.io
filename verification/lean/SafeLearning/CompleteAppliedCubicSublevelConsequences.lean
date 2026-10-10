import SafeLearning.CompleteAppliedCubicSublevel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SafeLearning.CompleteAppliedCubicSublevelConsequences
open CompleteAppliedCubicSublevel

theorem actual_cubic_ac_ode_solutions_are_unique_on_every_finite_interval
    (x y : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hxc : AbsolutelyContinuousOnInterval x 0 horizon)
    (hyc : AbsolutelyContinuousOnInterval y 0 horizon)
    (hxd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time)
    (hyd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt y (field (y time)) time)
    (hinitial : x 0 = y 0) : ∀ time ∈ Icc 0 horizon, x time = y time := by
  have hxc' : ContinuousOn x (Icc 0 horizon) := by
    simpa [uIcc_of_le hT] using hxc.continuousOn
  have hyc' : ContinuousOn y (Icc 0 horizon) := by
    simpa [uIcc_of_le hT] using hyc.continuousOn
  have hcoef : ContinuousOn
      (fun time : ℝ => -1 + (x time) ^ 2 + x time * y time + (y time) ^ 2)
      (Icc 0 horizon) := by fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hcoef
  have hdiff : AbsolutelyContinuousOnInterval (fun time => x time - y time) 0 horizon :=
    hxc.sub hyc
  have hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon →
      HasDerivAt (fun time => x time - y time) (field (x time) - field (y time)) time := by
    filter_upwards [hxd, hyd] with time hx hy ht
    exact (hx ht).sub (hy ht)
  have hb : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon →
      2 * (x time - y time) * (field (x time) - field (y time)) ≤
        -2 * (-K) * (x time - y time) ^ 2 := by
    exact Filter.Eventually.of_forall (fun time ht => by
      have hk := hK ⟨time, ht, rfl⟩
      have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg (x time - y time))
      rw [show field (x time) - field (y time) =
        (-1 + (x time) ^ 2 + x time * y time + (y time) ^ 2) * (x time - y time) by
          unfold field
          ring]
      nlinarith [hm])
  intro time ht
  have h := CompleteAppliedSmallGainStorage.actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    (fun time => x time - y time) (fun time => field (x time) - field (y time))
    (-K) horizon hT hdiff hd hb time ht
  simp only [hinitial, sub_self, abs_zero, zero_mul] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem actual_every_closed_unit_sublevel_ac_trajectory_equals_the_global_solution
    (x : ℝ → ℝ) (initial horizon : ℝ) (hi : initial ^ 2 ≤ 1) (hT : 0 ≤ horizon)
    (hc : AbsolutelyContinuousOnInterval x 0 horizon) (hx0 : x 0 = initial)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time) :
    ∀ time ∈ Icc 0 horizon, x time = actualSolution initial time := by
  have hs := actual_every_initial_in_the_closed_unit_sublevel_has_a_global_solution initial hi
  exact actual_cubic_ac_ode_solutions_are_unique_on_every_finite_interval
    x (actualSolution initial) horizon hT hc (hs.2.1 horizon hT) hd
    (Filter.Eventually.of_forall (fun time ht => hs.2.2 time ht.1))
    (hx0.trans hs.1.symm)

theorem actual_every_closed_sublevel_below_one_is_forward_invariant_for_ac_trajectories
    (x : ℝ → ℝ) (initial c horizon : ℝ) (hc1 : c ≤ 1)
    (hi : storage initial ≤ c) (hT : 0 ≤ horizon)
    (hc : AbsolutelyContinuousOnInterval x 0 horizon) (hx0 : x 0 = initial)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time)
    (time : ℝ) (ht : time ∈ Icc 0 horizon) : storage (x time) ≤ c := by
  have hi1 : initial ^ 2 ≤ 1 := (show initial ^ 2 ≤ c from hi).trans hc1
  rw [actual_every_closed_unit_sublevel_ac_trajectory_equals_the_global_solution
    x initial horizon hi1 hT hc hx0 hd time ht]
  have hm := actual_forward_solution_magnitude_does_not_exceed_initial_magnitude
    initial time hi1 ht.1
  have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hm
  have hs' : storage (actualSolution initial time) ≤ storage initial := by
    simpa only [sq_abs, storage] using hs
  exact hs'.trans hi

theorem actual_ac_sublevel_comparison_has_the_literal_storage_exponential_bound
    (x : ℝ → ℝ) (initial c horizon : ℝ) (hc1 : c ≤ 1)
    (hi : storage initial ≤ c) (hT : 0 ≤ horizon)
    (hc : AbsolutelyContinuousOnInterval x 0 horizon) (hx0 : x 0 = initial)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time)
    (time : ℝ) (ht : time ∈ Icc 0 horizon) :
    storage (x time) ≤ storage initial * Real.exp (-2 * (1 - c) * time) := by
  have hb : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon →
      2 * x time * field (x time) ≤ -2 * (1 - c) * (x time) ^ 2 := by
    exact Filter.Eventually.of_forall (fun time ht =>
      (actual_storage_derivative_and_sublevel_decrease (x time) c
        (actual_every_closed_sublevel_below_one_is_forward_invariant_for_ac_trajectories
          x initial c horizon hc1 hi hT hc hx0 hd time ht)).2.2)
  have hm := CompleteAppliedSmallGainStorage.actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    x (fun time => field (x time)) (1 - c) horizon hT hc hd hb time ht
  rw [hx0] at hm
  have hn : 0 ≤ |initial| * Real.exp (-(1 - c) * time) := by positivity
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).mpr hm
  have he : Real.exp (-(1 - c) * time) ^ 2 = Real.exp (-2 * (1 - c) * time) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, sq_abs, he, storage] using hs

theorem actual_global_solution_in_every_strict_unit_sublevel_tends_to_zero
    (initial : ℝ) (hi : initial ^ 2 < 1) :
    Tendsto (actualSolution initial) atTop (𝓝 0) := by
  have ht : Tendsto (fun time : ℝ => 2 * time) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have he := Real.tendsto_exp_atTop.comp ht
  have hd : Tendsto (denominator initial) atTop atTop :=
    tendsto_const_nhds.add_atTop (he.const_mul_atTop (sub_pos.mpr hi))
  exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hd)

theorem actual_every_global_ac_trajectory_in_a_strict_unit_sublevel_tends_to_zero
    (x : ℝ → ℝ) (initial c : ℝ) (hc1 : c < 1) (hi : storage initial ≤ c)
    (hc : ∀ horizon : ℝ, 0 ≤ horizon → AbsolutelyContinuousOnInterval x 0 horizon)
    (hx0 : x 0 = initial)
    (hd : ∀ horizon : ℝ, 0 ≤ horizon →
      ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time) :
    Tendsto x atTop (𝓝 0) := by
  have histrict : initial ^ 2 < 1 := (show initial ^ 2 ≤ c from hi).trans_lt hc1
  have heq : x =ᶠ[atTop] actualSolution initial := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with time ht
    exact actual_every_closed_unit_sublevel_ac_trajectory_equals_the_global_solution
      x initial time histrict.le ht (hc time ht) hx0 (hd time ht) time ⟨ht, le_rfl⟩
  exact (actual_global_solution_in_every_strict_unit_sublevel_tends_to_zero initial histrict).congr' heq.symm

theorem actual_unit_sublevel_boundary_equilibria_do_not_tend_to_zero :
    field 1 = 0 ∧ field (-1) = 0 ∧
      (∀ time : ℝ, actualSolution 1 time = 1 ∧ actualSolution (-1) time = -1) ∧
      ¬ Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) ∧
      ¬ Tendsto (fun _ : ℝ => (-1 : ℝ)) atTop (𝓝 0) := by
  refine ⟨by norm_num [field], by norm_num [field], ?_, ?_, ?_⟩
  · intro time
    norm_num [actualSolution, denominator]
  · intro ht
    have := tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)) ht
    norm_num at this
  · intro ht
    have := tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℝ => (-1 : ℝ)) atTop (𝓝 (-1))) ht
    norm_num at this

end SafeLearning.CompleteAppliedCubicSublevelConsequences
