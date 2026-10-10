import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSaturationSector
open scoped NNReal

/-- The actual scalar saturation from the systems primer. -/
def saturation (v : ℝ) : ℝ := max (-1) (min v 1)

theorem actual_saturation_middle_branch (v : ℝ) (hv : |v| ≤ 1) :
    saturation v = v := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hv
  simp only [saturation,min_eq_left hhi,max_eq_right hlo]

theorem actual_saturation_positive_branch (v : ℝ) (hv : 1 ≤ v) :
    saturation v = 1 := by
  simp [saturation,min_eq_right hv]

theorem actual_saturation_negative_branch (v : ℝ) (hv : v ≤ -1) :
    saturation v = -1 := by
  rw [saturation,min_eq_left (by linarith),max_eq_left hv]

theorem actual_saturation_outside_is_the_sign (v : ℝ) (hv : 1 < |v|) :
    saturation v = (if 0 ≤ v then 1 else -1) ∧ v*saturation v = |v| := by
  by_cases hp : 0 ≤ v
  · have hhi : 1 ≤ v := by rw [abs_of_nonneg hp] at hv;linarith
    rw [actual_saturation_positive_branch v hhi,ite_eq_left hp,abs_of_nonneg hp]
    simp
  · have hn : v < 0 := lt_of_not_ge hp
    have hlo : v ≤ -1 := by rw [abs_of_neg hn] at hv;linarith
    rw [actual_saturation_negative_branch v hlo,ite_eq_right hp,abs_of_neg hn]
    simp

theorem actual_saturation_is_globally_one_lipschitz : LipschitzWith 1 saturation := by
  exact (LipschitzWith.id.min_const (1:ℝ)).const_max (-1)

theorem actual_saturation_is_monotone : Monotone saturation := by
  intro v w h
  exact max_le_max le_rfl (min_le_min h le_rfl)

theorem actual_saturation_zero : saturation 0 = 0 := by norm_num [saturation]

theorem actual_every_pair_has_incremental_sector_zero_one (v w : ℝ) :
    0 ≤ (v-w)*(saturation v-saturation w) ∧
      (v-w)*(saturation v-saturation w) ≤ (v-w)^2 := by
  have hp : 0 ≤ (v-w)*(saturation v-saturation w) := by
    rcases le_total w v with h|h
    · exact mul_nonneg (sub_nonneg.mpr h)
        (sub_nonneg.mpr (actual_saturation_is_monotone h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (actual_saturation_is_monotone h))
  have ha : |saturation v-saturation w| ≤ |v-w| := by
    simpa [Real.dist_eq] using actual_saturation_is_globally_one_lipschitz.dist_le_mul v w
  have hab : (v-w)*(saturation v-saturation w) ≤ |v-w| * |saturation v-saturation w| := by
    simpa only [abs_mul] using le_abs_self ((v-w)*(saturation v-saturation w))
  have hupper := mul_le_mul_of_nonneg_left ha (abs_nonneg (v-w))
  have he : |v-w| * |v-w|=(v-w)^2 := by simpa only [pow_two] using sq_abs (v-w)
  exact ⟨hp,hab.trans (he ▸ hupper)⟩

theorem actual_every_input_has_origin_sector_zero_one (v : ℝ) :
    0 ≤ v*saturation v ∧ v*saturation v ≤ v^2 := by
  simpa only [actual_saturation_zero,sub_zero] using
    actual_every_pair_has_incremental_sector_zero_one v 0

theorem actual_source_middle_product (v : ℝ) (hv : |v| ≤ 1) :
    v*saturation v=v^2 ∧ 0 ≤ v*saturation v := by
  rw [actual_saturation_middle_branch v hv]
  exact ⟨by ring,mul_self_nonneg v⟩

theorem actual_source_outside_product (v : ℝ) (hv : 1 < |v|) :
    v*saturation v=|v| ∧ 0 ≤ |v| ∧ |v| ≤ v^2 := by
  have h := actual_saturation_outside_is_the_sign v hv
  have hs := actual_every_input_has_origin_sector_zero_one v
  exact ⟨h.2,abs_nonneg v,by simpa only [h.2] using hs.2⟩

theorem actual_nonzero_origin_slope_between_zero_and_one
    (v : ℝ) (hv : v ≠ 0) : 0 ≤ saturation v/v ∧ saturation v/v ≤ 1 := by
  have hs := actual_every_input_has_origin_sector_zero_one v
  have hp : 0 < v^2 := sq_pos_of_ne_zero hv
  have he : saturation v/v=(v*saturation v)/(v^2) := by
    field_simp
  rw [he]
  exact ⟨div_nonneg hs.1 hp.le,(div_le_one hp).mpr hs.2⟩

end SafeLearning.CompleteAppliedSaturationSector
