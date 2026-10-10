import SafeLearning.CompleteModulesGoSafeToyFeasibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyIslands
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility

def actualThreshold (gain : ℝ) : ℝ := 1/4+1/(2*gain)
def actualBoundary (gain : ℝ) : ℝ := Real.arccos (actualThreshold gain)/(4*Real.pi)

theorem actual_source_cosine_threshold_is_strictly_between_zero_and_one_half
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    0 < actualThreshold gain ∧ actualThreshold gain < 1/2 := by
  have hpos : 0 < 2*gain := by linarith [hg.1]
  have hl : 0 < 1/(2*gain) := div_pos (by norm_num) hpos
  have hu : 1/(2*gain) ≤ 1/6 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [hg.1]
  unfold actualThreshold
  constructor <;> linarith

theorem actual_cosine_sublevel_on_one_whole_period_is_an_interval
    (c theta : ℝ) (hc : c ∈ Icc (-1:ℝ) 1) (ht : theta ∈ Icc (0:ℝ) (2*Real.pi)) :
    Real.cos theta ≤ c ↔
      Real.arccos c ≤ theta ∧ theta ≤ 2*Real.pi-Real.arccos c := by
  have ha0 := Real.arccos_nonneg c
  have hap := Real.arccos_le_pi c
  have hcos := Real.cos_arccos hc.1 hc.2
  by_cases htpi : theta ≤ Real.pi
  · have hh : Real.cos theta ≤ c ↔ Real.arccos c ≤ theta := by
      conv_lhs => rw [← hcos]
      exact Real.strictAntiOn_cos.le_iff_ge ⟨ht.1,htpi⟩ ⟨ha0,hap⟩
    rw [hh]
    constructor
    · intro h
      exact ⟨h,by linarith⟩
    · exact And.left
  · have hu : 2*Real.pi-theta ∈ Icc (0:ℝ) Real.pi := ⟨by linarith [ht.2],by linarith⟩
    have hh : Real.cos theta ≤ c ↔ Real.arccos c ≤ 2*Real.pi-theta := by
      conv_lhs => rw [← Real.cos_two_pi_sub theta,← hcos]
      exact Real.strictAntiOn_cos.le_iff_ge hu ⟨ha0,hap⟩
    rw [hh]
    constructor
    · intro h
      exact ⟨by linarith,by linarith⟩
    · intro h
      linarith [h.2]

theorem actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) :
    (1/12:ℝ) < actualBoundary gain ∧ actualBoundary gain < 1/8 := by
  have hc := actual_source_cosine_threshold_is_strictly_between_zero_and_one_half gain hg
  have hhalf : Real.arccos (1/2)=Real.pi/3 := by
    apply Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
    exact Real.cos_pi_div_three.symm
  have hl := Real.arccos_lt_arccos (by linarith : -1 ≤ actualThreshold gain) hc.2 (by norm_num : (1/2:ℝ) ≤ 1)
  rw [hhalf] at hl
  have hu := Real.arccos_lt_arccos (by norm_num : (-1:ℝ) ≤ 0) hc.1 (by linarith : actualThreshold gain ≤ 1)
  rw [Real.arccos_zero] at hu
  unfold actualBoundary
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    nlinarith

theorem actual_source_safe_set_is_exactly_two_disjoint_closed_islands
    (gain a : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) (ha : a ∈ Icc (0:ℝ) 1) :
    0 ≤ actualSourceSafety gain a ↔
      a ∈ Icc (actualBoundary gain) (1/2-actualBoundary gain) ∪
        Icc (1/2+actualBoundary gain) (1-actualBoundary gain) := by
  rw [actual_source_feasibility_is_exactly_the_literal_cosine_threshold gain a hg]
  change Real.cos (4*Real.pi*a) ≤ actualThreshold gain ↔ _
  have hc := actual_source_cosine_threshold_is_strictly_between_zero_and_one_half gain hg
  have hcd : actualThreshold gain ∈ Icc (-1:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hb := actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth gain hg
  have hb0 : 0 < actualBoundary gain := by linarith [hb.1]
  have hid : Real.arccos (actualThreshold gain)=4*Real.pi*actualBoundary gain := by
    unfold actualBoundary
    field_simp
  have hp := Real.pi_pos
  by_cases hahalf : a ≤ 1/2
  · have ht : 4*Real.pi*a ∈ Icc (0:ℝ) (2*Real.pi) :=
      ⟨mul_nonneg (by positivity) ha.1,by nlinarith⟩
    rw [actual_cosine_sublevel_on_one_whole_period_is_an_interval _ _ hcd ht,hid]
    simp only [mem_union,mem_Icc]
    constructor
    · intro h
      left
      constructor <;> nlinarith [h.1,h.2]
    · intro h
      rcases h with h|h
      · constructor <;> nlinarith [h.1,h.2]
      · exfalso
        linarith [h.1]
  · have ht : 4*Real.pi*a-2*Real.pi ∈ Icc (0:ℝ) (2*Real.pi) := ⟨by nlinarith,by nlinarith [ha.2]⟩
    rw [← Real.cos_sub_two_pi (4*Real.pi*a),
      actual_cosine_sublevel_on_one_whole_period_is_an_interval _ _ hcd ht,hid]
    simp only [mem_union,mem_Icc]
    constructor
    · intro h
      right
      constructor <;> nlinarith [h.1,h.2]
    · intro h
      rcases h with h|h
      · exfalso
        linarith [h.2]
      · constructor <;> nlinarith [h.1,h.2]

theorem actual_safe_grid_columns_are_exactly_three_through_nine_and_fifteen_through_twenty_one
    (gain : ℝ) (hg : gain ∈ Icc (3:ℝ) 8) (i : Fin 25) :
    0 ≤ actualSourceSafety gain ((i.val:ℝ)/24) ↔
      (3 ≤ i.val ∧ i.val ≤ 9) ∨ (15 ≤ i.val ∧ i.val ≤ 21) := by
  have hb := actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth gain hg
  have ha : ((i.val:ℝ)/24) ∈ Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · have hi : (i.val:ℝ) ≤ 24 := by exact_mod_cast (by omega : i.val ≤ 24)
      linarith
  rw [actual_source_safe_set_is_exactly_two_disjoint_closed_islands gain _ hg ha]
  simp only [mem_union,mem_Icc]
  fin_cases i <;> norm_num <;> grind

end SafeLearning.CompleteModulesGoSafeToyIslands
