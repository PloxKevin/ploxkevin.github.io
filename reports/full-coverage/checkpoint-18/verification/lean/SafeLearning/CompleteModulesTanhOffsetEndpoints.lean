import SafeLearning.CompleteModulesTanhRefinement
import SafeLearning.CompleteModulesTanhSharpBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesTanhOffsetEndpoints
open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhAsymptotic
open CompleteModulesTanhSharpBounds CompleteModulesTanhRefinement

def offsetSlope (point center : ℝ) : ℝ :=
  (Real.tanh point-Real.tanh center)/(point-center)

theorem actual_tanh_derivative_is_nonincreasing_on_nonnegative_inputs
    (first second : ℝ) (hf : 0 ≤ first) (hs : first ≤ second) :
    1-(Real.tanh second)^2 ≤ 1-(Real.tanh first)^2 := by
  have hsecond : 0 ≤ second := hf.trans hs
  have hcosh : Real.cosh first ≤ Real.cosh second := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg hf,abs_of_nonneg hsecond] using hs
  rw [←actual_tanh_derivative_is_one_minus_square,
    ←actual_tanh_derivative_is_one_minus_square]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [Real.cosh_pos first,Real.cosh_pos second]

theorem actual_right_endpoint_chord_is_at_most_the_center_derivative
    (center right : ℝ) (hc : 0 ≤ center) (hr : center < right) :
    offsetSlope right center ≤ 1-(Real.tanh center)^2 := by
  obtain ⟨point,hp,he⟩ := actual_ordered_tanh_chord_has_a_genuine_mean_value_point center right hr
  rw [offsetSlope,he]
  exact actual_tanh_derivative_is_nonincreasing_on_nonnegative_inputs center point hc hp.1.le

def crossingSlope (center point : ℝ) : ℝ :=
  (Real.tanh point+Real.tanh center)/(point+center)

theorem actual_crossing_chord_is_antitone_beyond_a_positive_center
    (center : ℝ) (hc : 0 < center) :
    AntitoneOn (crossingSlope center) (Ici center) := by
  have hderiv (point : ℝ) (hp : point ∈ Ici center) :
      HasDerivAt (crossingSlope center)
        (((1-(Real.tanh point)^2)*(point+center)-(Real.tanh point+Real.tanh center))/(point+center)^2) point := by
    have hp0 : 0 < point := hc.trans_le hp
    have hn : point+center ≠ 0 := by positivity
    have ht := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative point).1
    convert (ht.add_const (Real.tanh center)).div ((hasDerivAt_id point).add_const center) hn using 1
    · funext z; rfl
    · simp only [id_eq,mul_one]
  apply antitoneOn_of_deriv_nonpos (convex_Ici center)
  · intro point hp
    exact (hderiv point hp).continuousAt.continuousWithinAt
  · intro point hp
    exact (hderiv point (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro point hp
    have hp' : point ∈ Ici center := interior_subset hp
    have hp0 : 0 < point := hc.trans_le hp'
    rw [(hderiv point hp').deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hpH := actual_source_h_is_positive_for_every_positive_input point hp0
    have hcH := actual_source_h_is_positive_for_every_positive_input center hc
    have hd := actual_tanh_derivative_is_nonincreasing_on_nonnegative_inputs center point hc.le hp'
    dsimp [sourceH] at hpH hcH
    nlinarith

theorem actual_offset_chords_have_the_minimum_endpoint_lower_bound_at_nonnegative_center
    (left center right point : ℝ) (hl : left < center) (hr : center < right)
    (hc : 0 ≤ center) (hp : point ∈ Icc left right) (hne : point ≠ center) :
    min (offsetSlope right center) (offsetSlope left center) ≤ offsetSlope point center := by
  by_cases hc0 : center = 0
  · subst center
    dsimp [offsetSlope]
    simp only [Real.tanh_zero,sub_zero]
    rcases lt_or_gt_of_ne hne with hnegative | hpositive
    · have hl0 : 0 < -left := by linarith
      have hp0 : 0 < -point := by linarith
      have hle : -point ≤ -left := by linarith [hp.1]
      have h := actual_tanh_origin_secant_is_antitone_on_positive_inputs hp0 hl0 hle
      change Real.tanh (-left) / (-left) ≤ Real.tanh (-point) / (-point) at h
      simp only [Real.tanh_neg,neg_div_neg_eq] at h
      exact (min_le_right _ _).trans h
    · exact (min_le_left _ _).trans
        (actual_tanh_origin_secant_is_antitone_on_positive_inputs hpositive hr hp.2)
  · have hcpos : 0 < center := lt_of_le_of_ne hc (Ne.symm hc0)
    rcases lt_or_gt_of_ne hne with hpointleft | hpointright
    · by_cases habs : |point| ≤ center
      · have hlocal := (actual_local_tanh_chord_has_the_literal_positive_lower_and_upper_bound
          center point center habs (by simpa only [abs_of_pos hcpos] using le_refl center) hne).2.1
        exact (min_le_left _ _).trans
          ((actual_right_endpoint_chord_is_at_most_the_center_derivative center right hc hr).trans hlocal)
      · have hnegative : point < 0 := by
          by_contra h
          have hn : 0 ≤ point := le_of_not_gt h
          apply habs
          rw [abs_of_nonneg hn]
          exact hpointleft.le
        have hfar : center < -point := by
          have h := lt_of_not_ge habs
          rwa [abs_of_neg hnegative] at h
        have hleftnegative : left < 0 := lt_of_le_of_lt hp.1 hnegative
        have hleftfar : center ≤ -left := by linarith [hp.1]
        have hanti := actual_crossing_chord_is_antitone_beyond_a_positive_center center hcpos
          (show -point ∈ Ici center from hfar.le) (show -left ∈ Ici center from hleftfar)
          (show -point ≤ -left by linarith [hp.1])
        have he (x : ℝ) : crossingSlope center (-x) = offsetSlope x center := by
          dsimp [crossingSlope,offsetSlope]
          rw [Real.tanh_neg]
          have hnum : -Real.tanh x+Real.tanh center = -(Real.tanh x-Real.tanh center) := by ring
          have hden : -x+center = -(x-center) := by ring
          rw [hnum,hden,neg_div_neg_eq]
        rw [he,he] at hanti
        exact (min_le_right _ _).trans hanti
    · have hanti := tanh_concave_nonnegative.antitoneOn_slope_gt
        (show center ∈ Ici 0 from hc)
      have h := hanti (show point ∈ {z ∈ Ici 0 | center < z} from ⟨(hc.trans hpointright.le),hpointright⟩)
        (show right ∈ {z ∈ Ici 0 | center < z} from ⟨hc.trans hr.le,hr⟩) hp.2
      exact (min_le_left _ _).trans (by simpa only [slope_def_field,offsetSlope] using h)

theorem actual_negated_offset_chord_has_the_same_slope (point center : ℝ) :
    offsetSlope (-point) (-center) = offsetSlope point center := by
  dsimp [offsetSlope]
  rw [Real.tanh_neg,Real.tanh_neg]
  have hnum : -Real.tanh point- -Real.tanh center = -(Real.tanh point-Real.tanh center) := by ring
  have hden : -point- -center = -(point-center) := by ring
  rw [hnum,hden,neg_div_neg_eq]

theorem actual_offset_chords_have_the_literal_minimum_endpoint_lower_bound
    (left center right point : ℝ) (hl : left < center) (hr : center < right)
    (hp : point ∈ Icc left right) (hne : point ≠ center) :
    min (offsetSlope right center) (offsetSlope left center) ≤ offsetSlope point center := by
  by_cases hc : 0 ≤ center
  · exact actual_offset_chords_have_the_minimum_endpoint_lower_bound_at_nonnegative_center
      left center right point hl hr hc hp hne
  · have h := actual_offset_chords_have_the_minimum_endpoint_lower_bound_at_nonnegative_center
      (-right) (-center) (-left) (-point) (by linarith) (by linarith) (by linarith)
      (show -point ∈ Icc (-right) (-left) by constructor <;> linarith [hp.1,hp.2])
      (by intro he; apply hne; linarith)
    rw [actual_negated_offset_chord_has_the_same_slope,
      actual_negated_offset_chord_has_the_same_slope,
      actual_negated_offset_chord_has_the_same_slope,min_comm] at h
    exact h

end SafeLearning.CompleteModulesTanhOffsetEndpoints
