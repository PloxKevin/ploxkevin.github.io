import SafeLearning.CompleteModulesTanhSharpBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesTanhSharpExtrema
open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhSharpBounds

def localChordLowerBounds (radius : ℝ) : Set ℝ :=
  {lower | ∀ first second : ℝ, |first| ≤ radius → |second| ≤ radius → first ≠ second →
    lower ≤ (Real.tanh first-Real.tanh second)/(first-second)}

def localChordUpperBounds (radius : ℝ) : Set ℝ :=
  {upper | ∀ first second : ℝ, |first| ≤ radius → |second| ≤ radius → first ≠ second →
    (Real.tanh first-Real.tanh second)/(first-second) ≤ upper}

theorem actual_local_chord_lower_bound_is_greatest
    (radius : ℝ) (hr : 0 < radius) :
    IsGreatest (localChordLowerBounds radius) (1-(Real.tanh radius)^2) := by
  refine ⟨?_,?_⟩
  · intro first second hf hs hne
    exact (actual_local_tanh_chord_has_the_literal_positive_lower_and_upper_bound
      radius first second hf hs hne).2.1
  · intro lower hlower
    apply ge_of_tendsto
      (actual_chords_near_the_positive_endpoint_approach_the_lower_derivative_bound radius)
    have hlow : ∀ᶠ point : ℝ in nhdsWithin radius (Iio radius), -radius < point :=
      (eventually_gt_nhds (by linarith : -radius < radius)).filter_mono nhdsWithin_le_nhds
    have hupp : ∀ᶠ point : ℝ in nhdsWithin radius (Iio radius), point < radius :=
      self_mem_nhdsWithin
    filter_upwards [hlow,hupp] with point hlo hup
    exact hlower point radius (abs_le.mpr ⟨hlo.le,hup.le⟩)
      (by simpa only [abs_of_pos hr] using le_refl radius) (ne_of_lt hup)

theorem actual_local_chord_upper_bound_is_least
    (radius : ℝ) (hr : 0 < radius) :
    IsLeast (localChordUpperBounds radius) 1 := by
  refine ⟨?_,?_⟩
  · intro first second _ _ hne
    exact (actual_tanh_chord_quotient_is_positive_and_at_most_one first second hne).2
  · intro upper hupper
    apply le_of_tendsto actual_chords_near_zero_approach_the_upper_derivative_bound
    have hlow : ∀ᶠ point : ℝ in nhdsWithin 0 (Ioi 0), 0 < point := self_mem_nhdsWithin
    have hupp : ∀ᶠ point : ℝ in nhdsWithin 0 (Ioi 0), point < radius :=
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlow,hupp] with point hlo hup
    exact hupper point 0 (by simpa only [abs_of_pos hlo] using hup.le)
      (by simpa only [abs_zero] using hr.le) (ne_of_gt hlo)

theorem actual_origin_sector_upper_bound_is_least
    (radius : ℝ) (hr : 0 < radius) :
    IsLeast {upper : ℝ | ∀ point : ℝ, point ≠ 0 → |point| ≤ radius →
      Real.tanh point/point ≤ upper} 1 := by
  refine ⟨?_,?_⟩
  · intro point hne _
    have h := (actual_tanh_chord_quotient_is_positive_and_at_most_one point 0 hne).2
    simpa only [Real.tanh_zero,sub_zero] using h
  · intro upper hupper
    apply le_of_tendsto
      (actual_origin_ratio_approaches_the_upper_endpoint_one_at_zero.mono_left
        (nhdsGT_le_nhdsNE 0))
    have hlow : ∀ᶠ point : ℝ in nhdsWithin 0 (Ioi 0), 0 < point := self_mem_nhdsWithin
    have hupp : ∀ᶠ point : ℝ in nhdsWithin 0 (Ioi 0), point < radius :=
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlow,hupp] with point hlo hup
    exact hupper point (ne_of_gt hlo) (by simpa only [abs_of_pos hlo] using hup.le)

def sourceRatio : ℝ → ℝ := Function.update (fun point : ℝ => Real.tanh point/point) 0 1

theorem actual_source_ratio_has_the_declared_zero_extension_and_nonzero_quotient :
    sourceRatio 0 = 1 ∧ ∀ point : ℝ, point ≠ 0 → sourceRatio point = Real.tanh point/point := by
  refine ⟨by simp [sourceRatio],?_⟩
  intro point hp
  exact Function.update_of_ne hp _ _

theorem actual_source_ratio_extension_is_continuous_at_zero :
    ContinuousAt sourceRatio 0 := by
  have h := (tanh_derivative 0).continuousAt_div
  simpa only [sourceRatio,Real.tanh_zero,Real.cosh_zero,sub_zero,one_pow,div_one] using h

theorem actual_source_ratio_extension_is_even (point : ℝ) :
    sourceRatio (-point) = sourceRatio point := by
  by_cases hp : point = 0
  · subst point; simp
  · have hn : -point ≠ 0 := neg_ne_zero.mpr hp
    simp only [sourceRatio,Function.update_of_ne hp,Function.update_of_ne hn,
      Real.tanh_neg,neg_div_neg_eq]

end SafeLearning.CompleteModulesTanhSharpExtrema
