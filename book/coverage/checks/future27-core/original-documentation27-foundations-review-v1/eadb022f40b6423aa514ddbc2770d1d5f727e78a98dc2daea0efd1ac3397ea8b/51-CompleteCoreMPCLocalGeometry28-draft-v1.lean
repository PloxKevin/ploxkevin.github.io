import SafeLearning.CompleteCoreMPCFirstSuccessor27
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteCoreMPCLocalGeometry28
open SafeLearning.CompleteCoreMPCNormBridge27
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- Actual linear rows with unit right-hand sides leave an explicit open ball
about zero in the state set. The zero-row case is covered by the same radius. -/
theorem actual_polytopic_state_set_contains_an_explicit_positive_origin_ball
    {I J : Type*} [Fintype I] [Fintype J] (H : Matrix J I ℝ) :
    0 < 1 / (‖H‖ + 1) ∧
    Metric.ball (0 : EuclideanSpace ℝ I) (1 / (‖H‖ + 1)) ⊆
      {x | ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1} := by
  have hdenom : 0 < ‖H‖ + 1 := by linarith [norm_nonneg H]
  have hr : 0 < 1 / (‖H‖ + 1) := div_pos zero_lt_one hdenom
  refine ⟨hr, ?_⟩
  intro x hx j
  have hxnorm : ‖x‖ < 1 / (‖H‖ + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hrow := actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H x j
  have hproduct : ‖H‖ * (1 / (‖H‖ + 1)) < 1 := by
    rw [mul_one_div]
    exact (div_lt_one hdenom).2 (by linarith)
  calc
    (H *ᵥ (fun i => x i)) j ≤ |(H *ᵥ (fun i => x i)) j| := le_abs_self _
    _ ≤ ‖H‖ * ‖x‖ := hrow
    _ ≤ ‖H‖ * (1 / (‖H‖ + 1)) :=
      mul_le_mul_of_nonneg_left hxnorm.le (norm_nonneg H)
    _ ≤ 1 := hproduct.le

/-- Continuity and a genuine positive-radius state neighbourhood give an
actual distinct local pair. Constants are ordered from the local inequalities,
rather than by asserting their order as an extra premise. The nontrivial state
space condition deliberately excludes the zero-dimensional degenerate case. -/
theorem actual_positive_origin_neighbourhood_and_local_tracking_bounds_order_constants
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [Nontrivial S]
    (X : Set S) (r delta cL cU : ℝ) (V : S → ℝ)
    (hr : 0 < r) (hball : Metric.ball (0 : S) r ⊆ X)
    (hdelta : 0 < delta) (hcontinuous : ContinuousOn V X) (hzero : V 0 = 0)
    (hlocal : ∀ x ∈ X, V x ≤ delta →
      cL * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ cU * ‖x‖ ^ 2) :
    ∃ x ∈ X, x ≠ 0 ∧ V x ≤ delta ∧ cL ≤ cU := by
  have hzeroX : (0 : S) ∈ X := hball (by simpa using hr)
  obtain ⟨s, hs, hsmall⟩ :=
    (Metric.continuousWithinAt_iff.mp (hcontinuous 0 hzeroX)) delta hdelta
  have hmin : 0 < min r s := lt_min hr hs
  have hhalf : 0 < min r s / 2 := by linarith
  obtain ⟨x, hxnorm⟩ := exists_norm_eq S hhalf.le
  have hxX : x ∈ X := hball (by
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hxnorm]
    have := min_le_left r s
    linarith)
  have hxs : dist x 0 < s := by
    rw [dist_zero_right, hxnorm]
    have := min_le_right r s
    linarith
  have hval : V x ≤ delta := by
    have hd := hsmall hxX hxs
    rw [hzero, dist_zero_right, Real.norm_eq_abs] at hd
    exact (le_abs_self (V x)).trans hd.le
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    linarith
  have hb := hlocal x hxX hval
  have horder : cL ≤ cU := by
    have hsq : 0 < ‖x‖ ^ 2 := by rw [hxnorm]; positivity
    exact (mul_le_mul_iff_left₀ hsq).mp (hb.1.trans hb.2)
  exact ⟨x, hxX, hxne, hval, horder⟩

def actualInputErosion {A : Type*} [Add A] (U W : Set A) : Set A :=
  {u | ∀ d ∈ W, u + d ∈ U}

/-- The actual Pontryagin-difference relation supplies both Assumption2 input
domain conditions. A perturbed input domain conclusion is proved here. -/
theorem actual_eroded_input_and_bounded_error_are_both_admissible
    {A : Type*} [NormedAddCommGroup A] (U : Set A) (eta : ℝ)
    (heta : 0 ≤ eta) (u d : A)
    (hu : u ∈ actualInputErosion U {e | ‖e‖ ≤ eta}) (hd : ‖d‖ ≤ eta) :
    u ∈ U ∧ u + d ∈ U := by
  constructor
  · simpa using hu 0 (by simpa using heta)
  · exact hu d hd

/-- This row calculation uses only the actual input tightening and its error
bound; it does not assume that the updated input already meets the constraints. -/
theorem actual_one_row_tightening_increment_covers_the_input_error
    (oldRow errorRow epsilonEarlier epsilonLater increment : ℝ)
    (hold : oldRow ≤ 1 - epsilonLater)
    (herror : errorRow ≤ increment)
    (hincrement : epsilonLater = epsilonEarlier + increment) :
    oldRow + errorRow ≤ 1 - epsilonEarlier := by
  linarith

end SafeLearning.CompleteCoreMPCLocalGeometry28
