import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedDiscreteQuadraticBasin

def sourceMap (x : ℝ) : ℝ := (1/2)*x+x^2

def actualTrajectory (initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n+1 => sourceMap (actualTrajectory initial n)

theorem actual_source_map_factorization (x : ℝ) :
    sourceMap x=x*((1/2)+x) := by
  unfold sourceMap
  ring

theorem actual_every_source_recurrence_is_the_constructed_trajectory
    (initial : ℝ) (x : ℕ → ℝ) (h0 : x 0=initial)
    (hstep : ∀ n, x (n+1)=sourceMap (x n)) : x=actualTrajectory initial := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => simpa [actualTrajectory,ih] using hstep n

theorem actual_source_fixed_points_are_exactly_zero_and_one_half (x : ℝ) :
    sourceMap x=x ↔ x=0 ∨ x=1/2 := by
  unfold sourceMap
  constructor
  · intro h
    have hp : x*(x-1/2)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem actual_source_derivative (x : ℝ) :
    HasDerivAt sourceMap ((1/2)+2*x) x := by
  have h := ((hasDerivAt_id x).const_mul (1/2)).add ((hasDerivAt_id x).pow 2)
  convert h using 1
  · funext y
    simp [sourceMap]
  · simp

theorem actual_source_storage_difference (x : ℝ) :
    (sourceMap x)^2-x^2=x^2*(((1/2)+x)^2-1) := by
  rw [actual_source_map_factorization]
  ring

theorem actual_storage_strict_decrease_iff (x : ℝ) :
    (sourceMap x)^2-x^2 < 0 ↔ x≠0 ∧ -3/2 < x ∧ x < 1/2 := by
  rw [actual_source_storage_difference]
  constructor
  · intro h
    have hx : x≠0 := by intro hz; subst x; norm_num at h
    have hx2 := sq_pos_of_ne_zero hx
    have hf : ((1/2:ℝ)+x)^2-1 < 0 := (mul_neg_iff.mp h).resolve_right
      (by rintro ⟨hn,_⟩; nlinarith [sq_nonneg x]) |>.2
    refine ⟨hx,?_,?_⟩ <;> nlinarith [sq_nonneg (x+3/2),sq_nonneg (x-1/2)]
  · rintro ⟨hx,hlo,hhi⟩
    have hf : ((1/2:ℝ)+x)^2-1 < 0 := by
      have hm := mul_neg_of_pos_of_neg (by linarith : 0 < x+3/2)
        (by linarith : x-1/2 < 0)
      nlinarith
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hx) hf

theorem actual_map_has_the_true_global_minimum (x : ℝ) :
    -1/16 ≤ sourceMap x := by
  unfold sourceMap
  nlinarith [sq_nonneg (x+1/4)]

theorem actual_compact_interval_is_invariant
    (upper x : ℝ) (hu0 : 0 ≤ upper) (hu : upper < 1/2)
    (hx : x ∈ Icc (-1/16) upper) :
    sourceMap x ∈ Icc (-1/16) upper := by
  refine ⟨actual_map_has_the_true_global_minimum x,?_⟩
  rw [actual_source_map_factorization]
  by_cases hx0 : x ≤ 0
  · have hf : 0 ≤ (1/2:ℝ)+x := by linarith [hx.1]
    exact (mul_nonpos_of_nonpos_of_nonneg hx0 hf).trans hu0
  · have hxpos : 0 ≤ x := le_of_lt (lt_of_not_ge hx0)
    have hf : (1/2:ℝ)+x ≤ 1 := by linarith [hx.2]
    have hm := mul_le_mul_of_nonneg_left hf hxpos
    simpa only [mul_one] using hm.trans (by simpa only [mul_one] using hx.2)

theorem actual_map_contracts_magnitude_on_each_compact_basin_interval
    (upper x : ℝ) (_hu0 : 0 ≤ upper) (_hu : upper < 1/2)
    (hx : x ∈ Icc (-1/16) upper) :
    |sourceMap x| ≤ ((1/2)+upper)*|x| := by
  have hf : 0 ≤ (1/2:ℝ)+x := by linarith [hx.1]
  rw [actual_source_map_factorization,abs_mul,abs_of_nonneg hf]
  have hm := mul_le_mul_of_nonneg_left (show (1/2:ℝ)+x ≤ (1/2)+upper by
    linarith [hx.2]) (abs_nonneg x)
  nlinarith

theorem actual_compact_basin_trajectory_remains_and_has_geometric_bound
    (upper initial : ℝ) (hu0 : 0 ≤ upper) (hu : upper < 1/2)
    (hi : initial ∈ Icc (-1/16) upper) (n : ℕ) :
    actualTrajectory initial n ∈ Icc (-1/16) upper ∧
      |actualTrajectory initial n| ≤ ((1/2)+upper)^n*|initial| := by
  induction n with
  | zero => simpa [actualTrajectory] using And.intro hi (le_refl |initial|)
  | succ n ih =>
    refine ⟨actual_compact_interval_is_invariant upper _ hu0 hu ih.1,?_⟩
    have hc := actual_map_contracts_magnitude_on_each_compact_basin_interval
      upper _ hu0 hu ih.1
    have hq : 0 ≤ (1/2:ℝ)+upper := by linarith
    have hm := mul_le_mul_of_nonneg_left ih.2 hq
    change |sourceMap (actualTrajectory initial n)| ≤ _
    calc
      _ ≤ ((1/2)+upper)*|actualTrajectory initial n| := hc
      _ ≤ ((1/2)+upper)*(((1/2)+upper)^n*|initial|) := hm
      _ = ((1/2)+upper)^(n+1)*|initial| := by rw [pow_succ]; ring

theorem actual_every_compact_basin_trajectory_tends_to_zero
    (upper initial : ℝ) (hu0 : 0 ≤ upper) (hu : upper < 1/2)
    (hi : initial ∈ Icc (-1/16) upper) :
    Tendsto (actualTrajectory initial) atTop (𝓝 0) := by
  have hq0 : 0 ≤ (1/2:ℝ)+upper := by linarith
  have hq1 : (1/2:ℝ)+upper < 1 := by linarith
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const |initial|
  have ha : Tendsto (fun n => |actualTrajectory initial n|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) (fun n =>
      (actual_compact_basin_trajectory_remains_and_has_geometric_bound
        upper initial hu0 hu hi n).2)
    simpa using hg
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using ha)

theorem actual_trajectory_after_one_step_is_the_shifted_constructed_trajectory
    (initial : ℝ) (n : ℕ) :
    actualTrajectory initial (n+1)=actualTrajectory (sourceMap initial) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sourceMap (actualTrajectory initial (n+1)) =
      sourceMap (actualTrajectory (sourceMap initial) n)
    rw [ih]

theorem actual_every_initial_in_the_true_open_basin_tends_to_zero
    (initial : ℝ) (hi : initial ∈ Ioo (-1) (1/2)) :
    Tendsto (actualTrajectory initial) atTop (𝓝 0) := by
  have hf : sourceMap initial < 1/2 := by
    have hp := mul_neg_of_pos_of_neg (by linarith [hi.1] : 0 < initial+1)
      (by linarith [hi.2] : initial-1/2 < 0)
    unfold sourceMap
    nlinarith
  let upper := max (sourceMap initial) 0
  have hu0 : 0 ≤ upper := le_max_right _ _
  have hu : upper < 1/2 := max_lt_iff.mpr ⟨hf,by norm_num⟩
  have hstart : sourceMap initial ∈ Icc (-1/16) upper :=
    ⟨actual_map_has_the_true_global_minimum initial,le_max_left _ _⟩
  have htail := actual_every_compact_basin_trajectory_tends_to_zero
    upper (sourceMap initial) hu0 hu hstart
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [actual_trajectory_after_one_step_is_the_shifted_constructed_trajectory] using htail

theorem actual_half_boundary_is_a_nonzero_constant_trajectory (n : ℕ) :
    actualTrajectory (1/2) n=1/2 := by
  induction n with
  | zero => rfl
  | succ n ih => norm_num [actualTrajectory,ih,sourceMap]

theorem actual_negative_boundary_maps_to_the_nonzero_fixed_point (n : ℕ) :
    actualTrajectory (-1) (n+1)=1/2 := by
  rw [actual_trajectory_after_one_step_is_the_shifted_constructed_trajectory]
  norm_num [sourceMap,actual_half_boundary_is_a_nonzero_constant_trajectory]

theorem actual_above_boundary_trajectory_has_a_genuine_geometric_growth_bound
    (initial : ℝ) (hi : 1/2 < initial) (n : ℕ) :
    initial ≤ actualTrajectory initial n ∧
      ((1/2)+initial)^n*initial ≤ actualTrajectory initial n := by
  induction n with
  | zero => simp [actualTrajectory]
  | succ n ih =>
    have hi0 : 0 ≤ initial := by linarith
    have hx0 : 0 ≤ actualTrajectory initial n := hi0.trans ih.1
    have hfactor : 1 ≤ (1/2:ℝ)+actualTrajectory initial n := by linarith [ih.1]
    have hmono := mul_le_mul_of_nonneg_left hfactor hx0
    have hq0 : 0 ≤ (1/2:ℝ)+initial := by linarith
    have hprod := mul_le_mul_of_nonneg_left
      (show (1/2:ℝ)+initial ≤ (1/2)+actualTrajectory initial n by linarith [ih.1]) hx0
    have hbound := mul_le_mul_of_nonneg_left ih.2 hq0
    rw [actualTrajectory,actual_source_map_factorization]
    refine ⟨?_,?_⟩
    · simpa only [mul_one] using
        (show initial ≤ actualTrajectory initial n*1 by simpa only [mul_one] using ih.1).trans hmono
    · rw [pow_succ]
      nlinarith

theorem actual_every_initial_above_the_boundary_tends_to_positive_infinity
    (initial : ℝ) (hi : 1/2 < initial) :
    Tendsto (actualTrajectory initial) atTop atTop := by
  have hq : 1 < (1/2:ℝ)+initial := by linarith
  have hi0 : 0 < initial := by linarith
  have hg := (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const' hi0
  exact tendsto_atTop_mono
    (fun n => (actual_above_boundary_trajectory_has_a_genuine_geometric_growth_bound
      initial hi n).2) hg

theorem actual_every_initial_below_the_negative_boundary_tends_to_positive_infinity
    (initial : ℝ) (hi : initial < -1) :
    Tendsto (actualTrajectory initial) atTop atTop := by
  have hf : 1/2 < sourceMap initial := by
    have hp := mul_pos_of_neg_of_neg (by linarith : initial+1 < 0)
      (by linarith : initial-1/2 < 0)
    unfold sourceMap
    nlinarith
  have ht := actual_every_initial_above_the_boundary_tends_to_positive_infinity
    (sourceMap initial) hf
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [actual_trajectory_after_one_step_is_the_shifted_constructed_trajectory] using ht

theorem actual_convergence_basin_is_exactly_the_printed_open_interval
    (initial : ℝ) :
    Tendsto (actualTrajectory initial) atTop (𝓝 0) ↔ initial ∈ Ioo (-1) (1/2) := by
  constructor
  · intro ht
    have htail := (tendsto_add_atTop_iff_nat 1).mpr ht
    by_contra hn
    have hout : initial ≤ -1 ∨ 1/2 ≤ initial := by
      simp only [mem_Ioo,not_and_or,not_lt] at hn
      exact hn
    rcases hout with hlo | hhi
    · rcases lt_or_eq_of_le hlo with hlo | rfl
      · have htop := actual_every_initial_below_the_negative_boundary_tends_to_positive_infinity
          initial hlo
        exact not_tendsto_nhds_of_tendsto_atTop htop 0 ht
      · have hc : Tendsto (fun _ : ℕ => (1/2:ℝ)) atTop (𝓝 (0:ℝ)) := by
          simpa only [actual_negative_boundary_maps_to_the_nonzero_fixed_point] using htail
        have he := tendsto_nhds_unique hc tendsto_const_nhds
        norm_num at he
    · rcases lt_or_eq_of_le hhi with hhi | hhi
      · have htop := actual_every_initial_above_the_boundary_tends_to_positive_infinity initial hhi
        exact not_tendsto_nhds_of_tendsto_atTop htop 0 ht
      · subst initial
        have hc : Tendsto (fun _ : ℕ => (1/2:ℝ)) atTop (𝓝 (0:ℝ)) := by
          convert ht using 1
          funext n
          exact (actual_half_boundary_is_a_nonzero_constant_trajectory n).symm
        have he := tendsto_nhds_unique hc tendsto_const_nhds
        norm_num at he
  · exact actual_every_initial_in_the_true_open_basin_tends_to_zero initial

end SafeLearning.CompleteAppliedDiscreteQuadraticBasin
