import SafeLearning.CompleteAppliedSmallGainStorage

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SafeLearning.CompleteAppliedGlobalLipschitzACUniqueness

theorem actual_globally_lipschitz_field_has_unique_existing_ac_solutions
    (field : ℝ → ℝ) (K : ℝ≥0) (hfield : LipschitzWith K field)
    (x y : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hxc : AbsolutelyContinuousOnInterval x 0 horizon)
    (hyc : AbsolutelyContinuousOnInterval y 0 horizon)
    (hxd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time)
    (hyd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt y (field (y time)) time)
    (hinitial : x 0 = y 0) : ∀ time ∈ Icc 0 horizon, x time = y time := by
  have hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon →
      HasDerivAt (fun t => x t - y t) (field (x time) - field (y time)) time := by
    filter_upwards [hxd, hyd] with time hx hy ht
    exact (hx ht).sub (hy ht)
  have hb : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon →
      2 * (x time - y time) * (field (x time) - field (y time)) ≤
        -2 * (-(K : ℝ)) * (x time - y time) ^ 2 := by
    apply Filter.Eventually.of_forall
    intro time _
    have hl : |field (x time) - field (y time)| ≤ (K : ℝ) * |x time - y time| := by
      simpa only [Real.dist_eq] using hfield.dist_le_mul (x time) (y time)
    have hp : (x time - y time) * (field (x time) - field (y time)) ≤
        (K : ℝ) * (x time - y time) ^ 2 := by
      calc
        _ ≤ |(x time - y time) * (field (x time) - field (y time))| := le_abs_self _
        _ = |x time - y time| * |field (x time) - field (y time)| := abs_mul _ _
        _ ≤ |x time - y time| * ((K : ℝ) * |x time - y time|) :=
          mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        _ = (K : ℝ) * (x time - y time) ^ 2 := by rw [mul_left_comm, ← pow_two, sq_abs]
    nlinarith
  intro time ht
  have h := CompleteAppliedSmallGainStorage.actual_existing_ac_trajectory_square_decrease_implies_the_true_norm_bound
    (fun time => x time - y time) (fun time => field (x time) - field (y time))
    (-(K : ℝ)) horizon hT (hxc.sub hyc) hd hb time ht
  simp only [hinitial, sub_self, abs_zero, zero_mul] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end SafeLearning.CompleteAppliedGlobalLipschitzACUniqueness
