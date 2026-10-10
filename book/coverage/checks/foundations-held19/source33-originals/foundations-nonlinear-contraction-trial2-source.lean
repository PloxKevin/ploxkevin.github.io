import SafeLearning.CompleteFoundationsNonlinearDecreasingModel

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsNonlinearContraction
open CompleteFoundationsNonlinearDecreasingModel

theorem actual_source_derivative_at_every_real_state (x : ℝ) :
    HasDerivAt sourceMap ((1-x^2)/(1+x^2)^2) x := by
  have hd : 1+x^2 ≠ 0 := ne_of_gt (by positivity)
  convert (hasDerivAt_id x).div
    ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)) hd using 1
  · rfl
  · dsimp only [id_eq, Pi.add_apply, Pi.pow_apply]
    congr 1
    ring

theorem actual_source_derivative_at_zero_is_exactly_one :
    HasDerivAt sourceMap 1 0 := by
  simpa using actual_source_derivative_at_every_real_state 0

theorem actual_source_absolute_value_strictly_decreases_at_every_nonzero_state
    (x : ℝ) (hx : x ≠ 0) : |sourceMap x| < |x| := by
  have hs : 0 < x^2 := sq_pos_of_ne_zero hx
  have ha : 0 < |x| := abs_pos.mpr hx
  rw [sourceMap,abs_div,abs_of_pos (by positivity : 0 < 1+x^2)]
  apply (div_lt_iff₀ (by positivity : 0 < 1+x^2)).mpr
  nlinarith

theorem actual_source_zero_is_the_only_fixed_point (x : ℝ) :
    sourceMap x = x ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hd := actual_source_absolute_value_strictly_decreases_at_every_nonzero_state x hx
    rw [h] at hd
    exact lt_irrefl _ hd
  · intro h
    subst x
    norm_num [sourceMap]

theorem actual_no_factor_less_than_one_bounds_source_distances_on_any_zero_neighborhood
    (L delta : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1) (hdelta : 0 < delta) :
    ¬ (∀ x ∈ Ioo (-delta) delta, ∀ y ∈ Ioo (-delta) delta,
      |sourceMap x-sourceMap y| ≤ L*|x-y|) := by
  intro h
  have hzero : (0:ℝ) ∈ Ioo (-delta) delta := ⟨by linarith,hdelta⟩
  have hnhds : Ioo (-delta) delta ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds hzero.1 hzero.2
  have hevent : ∀ᶠ x in 𝓝 (0:ℝ), ‖sourceMap x-sourceMap 0‖ ≤ L*‖x-0‖ := by
    filter_upwards [hnhds] with x hx
    simpa only [Real.norm_eq_abs] using h x hx 0 hzero
  have hd := actual_source_derivative_at_zero_is_exactly_one.le_of_lip' hL0 hevent
  norm_num at hd
  linarith

theorem actual_no_strict_global_contraction_factor_exists :
    ¬ ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧ ∀ x y : ℝ,
      |sourceMap x-sourceMap y| ≤ L*|x-y| := by
  rintro ⟨L,hL0,hL1,h⟩
  apply actual_no_factor_less_than_one_bounds_source_distances_on_any_zero_neighborhood
    L 1 hL0 hL1 (by norm_num)
  exact fun x _ y _ => h x y

theorem actual_no_uniform_geometric_incremental_bound_even_on_any_zero_neighborhood
    (q delta : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hdelta : 0 < delta) :
    ¬ (∀ x ∈ Ioo (-delta) delta, ∀ y ∈ Ioo (-delta) delta, ∀ n : ℕ,
      |sourceMap^[n] x-sourceMap^[n] y| ≤ q^n*|x-y|) := by
  intro h
  apply actual_no_factor_less_than_one_bounds_source_distances_on_any_zero_neighborhood
    q delta hq0 hq1 hdelta
  intro x hx y hy
  simpa only [Function.iterate_one,pow_one] using h x hx y hy 1

theorem actual_every_initial_trajectory_converges_despite_no_strict_contraction :
    (∀ initial : ℝ, Tendsto (fun n => sourceMap^[n] initial) atTop (𝓝 0)) ∧
      ¬ ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧ ∀ x y : ℝ,
        |sourceMap x-sourceMap y| ≤ L*|x-y| := by
  refine ⟨?_,actual_no_strict_global_contraction_factor_exists⟩
  intro initial
  exact (actual_every_source_recurrence_from_every_initial_state_converges_to_zero
    (fun n => sourceMap^[n] initial) (fun n => Function.iterate_succ_apply' _ _ _)).1

end SafeLearning.CompleteFoundationsNonlinearContraction
