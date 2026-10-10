import SafeLearning.CompleteAppliedDiscreteLyapunovMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedDiscreteBasinConsequences
open CompleteAppliedDiscreteQuadraticBasin CompleteAppliedDiscreteLyapunovMatrix

theorem actual_source_boundary_value_and_repelling_derivative :
    sourceMap (-1)=1/2 ∧ HasDerivAt sourceMap (3/2) (1/2) ∧ (1:ℝ)<3/2 := by
  refine ⟨by norm_num [sourceMap],?_,by norm_num⟩
  convert actual_source_derivative (1/2) using 1; norm_num

theorem actual_every_inside_initial_first_enters_the_true_small_interval
    (initial : ℝ) (hi : initial∈Ioo (-1) (1/2)) :
    sourceMap initial∈Ico (-1/16) (1/2) := by
  refine ⟨actual_map_has_the_true_global_minimum initial,?_⟩
  have hm := mul_neg_of_pos_of_neg (by linarith [hi.1] : 0 < initial+1)
    (by linarith [hi.2] : initial-1/2<0)
  unfold sourceMap
  nlinarith

theorem actual_each_certified_sublevel_is_forward_invariant
    (c initial : ℝ) (hc : 0≤c) (hsmall : c<1/4) (hi : initial^2≤c) :
    ∀n, (actualTrajectory initial n)^2≤c := by
  have hstep (x : ℝ) (hx : x^2≤c) : (sourceMap x)^2≤c := by
    by_cases hz : x=0
    · subst x
      simpa [sourceMap] using hc
    · have hlo : -3/2<x := by nlinarith [sq_nonneg (x+1/2)]
      have hhi : x<1/2 := by nlinarith [sq_nonneg (x-1/2)]
      have hd := (actual_storage_strict_decrease_iff x).mpr ⟨hz,hlo,hhi⟩
      linarith
  intro n
  induction n with
  | zero => exact hi
  | succ n ih => exact hstep _ ih

theorem actual_each_certified_sublevel_trajectory_really_converges
    (c initial : ℝ) (_hc : 0≤c) (hsmall : c<1/4) (hi : initial^2≤c) :
    Tendsto (actualTrajectory initial) atTop (𝓝 0) := by
  apply actual_every_initial_in_the_true_open_basin_tends_to_zero initial
  constructor <;> nlinarith [sq_nonneg (initial+1/2),sq_nonneg (initial-1/2)]

def stableAtHalf : Prop := ∀epsilon : ℝ, 0<epsilon → ∃delta : ℝ, 0<delta ∧
  ∀initial : ℝ, |initial-1/2|<delta → ∀n, |actualTrajectory initial n-1/2|<epsilon

theorem actual_half_fixed_point_is_unstable_in_every_neighborhood : ¬stableAtHalf := by
  intro hs
  obtain ⟨delta,hd,hbound⟩ := hs 1 (by norm_num)
  let initial : ℝ := (1/2)+delta/2
  have hi : (1/2:ℝ) < initial := by dsimp [initial]; linarith
  have hnear : |initial-1/2|<delta := by
    have he : initial-1/2=delta/2 := by dsimp [initial];ring
    rw [he,abs_of_pos (by linarith : 0<delta/2)]
    linarith
  have ht := actual_every_initial_above_the_boundary_tends_to_positive_infinity initial hi
  obtain ⟨n,hn⟩ := (ht.eventually_gt_atTop (3/2)).exists
  have hb := hbound initial hnear n
  have ha := le_abs_self (actualTrajectory initial n-1/2)
  linarith

theorem actual_negative_square_levels_are_empty (c : ℝ) (hc : c<0) :
    {x : ℝ | x^2≤c}=∅ := by
  ext x
  simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
  intro hx
  nlinarith [sq_nonneg x]

theorem actual_small_interval_magnitude_strictly_decreases_except_at_zero
    (upper x : ℝ) (hu0 : 0≤upper) (hu : upper<1/2)
    (hx : x∈Icc (-1/16) upper) (hn : x≠0) :
    |sourceMap x| < |x| := by
  have hb := actual_map_contracts_magnitude_on_each_compact_basin_interval upper x hu0 hu hx
  have hp : 0 < |x| := abs_pos.mpr hn
  have hm := mul_lt_mul_of_pos_right (show (1/2:ℝ)+upper<1 by linarith) hp
  exact hb.trans_lt (by simpa only [one_mul] using hm)

end SafeLearning.CompleteAppliedDiscreteBasinConsequences
