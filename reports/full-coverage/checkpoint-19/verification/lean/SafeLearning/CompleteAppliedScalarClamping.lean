import SafeLearning.CompleteAppliedGlobalLipschitzACUniqueness
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedScalarClamping

def clamp (radius state : ℝ) : ℝ := max (-radius) (min radius state)

theorem actual_clamp_is_globally_one_lipschitz (radius : ℝ) :
    LipschitzWith 1 (clamp radius) :=
  (LipschitzWith.id.const_min radius).const_max (-radius)

theorem actual_clamp_is_in_the_closed_interval (radius state : ℝ) (hr : 0 ≤ radius) :
    clamp radius state ∈ Icc (-radius) radius := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem actual_clamp_fixes_every_point_in_the_closed_interval (radius state : ℝ)
    (hs : state ∈ Icc (-radius) radius) : clamp radius state = state := by
  simp [clamp, min_eq_right hs.2, max_eq_right hs.1]

theorem actual_locally_lipschitz_function_composed_with_clamp_is_globally_lipschitz
    (field : ℝ → ℝ) (hl : LocallyLipschitz field) (radius : ℝ) (hr : 0 ≤ radius) :
    ∃ K : ℝ≥0, LipschitzWith K (fun state => field (clamp radius state)) := by
  obtain ⟨K, hK⟩ := hl.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := Icc (-radius) radius) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hp := hK.dist_le_mul (clamp radius x) (actual_clamp_is_in_the_closed_interval radius x hr)
    (clamp radius y) (actual_clamp_is_in_the_closed_interval radius y hr)
  have hc := (actual_clamp_is_globally_one_lipschitz radius).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at hc
  exact hp.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg)

theorem actual_locally_lipschitz_field_has_unique_existing_ac_solutions
    (field : ℝ → ℝ) (hl : LocallyLipschitz field)
    (x y : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hxc : AbsolutelyContinuousOnInterval x 0 horizon)
    (hyc : AbsolutelyContinuousOnInterval y 0 horizon)
    (hxd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (field (x time)) time)
    (hyd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt y (field (y time)) time)
    (hinitial : x 0 = y 0) : EqOn x y (Icc 0 horizon) := by
  have hxc' : ContinuousOn x (Icc 0 horizon) := by
    simpa [uIcc_of_le hT] using hxc.continuousOn
  have hyc' : ContinuousOn y (Icc 0 horizon) := by
    simpa [uIcc_of_le hT] using hyc.continuousOn
  obtain ⟨Kx, hKx⟩ := isCompact_Icc.bddAbove_image hxc'.abs
  obtain ⟨Ky, hKy⟩ := isCompact_Icc.bddAbove_image hyc'.abs
  let radius := max 0 (max Kx Ky) + 1
  have hr : 0 ≤ radius := by dsimp [radius]; have := le_max_left 0 (max Kx Ky); linarith
  have hxmem : ∀ time ∈ Icc 0 horizon, x time ∈ Icc (-radius) radius := by
    intro time ht
    have hb := hKx ⟨time, ht, rfl⟩
    have hk : Kx ≤ radius := by
      dsimp [radius]
      exact (le_max_left Kx Ky).trans ((le_max_right 0 _).trans (by linarith))
    exact abs_le.mp (hb.trans hk)
  have hymem : ∀ time ∈ Icc 0 horizon, y time ∈ Icc (-radius) radius := by
    intro time ht
    have hb := hKy ⟨time, ht, rfl⟩
    have hk : Ky ≤ radius := by
      dsimp [radius]
      exact (le_max_right Kx Ky).trans ((le_max_right 0 _).trans (by linarith))
    exact abs_le.mp (hb.trans hk)
  obtain ⟨K, hK⟩ := actual_locally_lipschitz_function_composed_with_clamp_is_globally_lipschitz
    field hl radius hr
  apply CompleteAppliedGlobalLipschitzACUniqueness.actual_globally_lipschitz_field_has_unique_existing_ac_solutions
    (fun state => field (clamp radius state)) K hK x y horizon hT hxc hyc _ _ hinitial
  · filter_upwards [hxd] with time hd ht
    simpa only [actual_clamp_fixes_every_point_in_the_closed_interval radius _ (hxmem time ht)] using hd ht
  · filter_upwards [hyd] with time hd ht
    simpa only [actual_clamp_fixes_every_point_in_the_closed_interval radius _ (hymem time ht)] using hd ht

end SafeLearning.CompleteAppliedScalarClamping
