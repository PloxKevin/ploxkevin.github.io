import SafeLearning.CompleteModulesTanhAsymptotic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesTanhSharpBounds
open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhAsymptotic

theorem actual_tanh_derivative_strictly_decreases_on_positive_inputs :
    StrictAntiOn (deriv Real.tanh) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hcosh : Real.cosh x < Real.cosh y := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_pos hx0,abs_of_pos hy0] using hxy
  rw [(tanh_derivative x).deriv,(tanh_derivative y).deriv]
  apply one_div_lt_one_div_of_lt
  · positivity
  · nlinarith [Real.cosh_pos x,Real.cosh_pos y]

theorem actual_tanh_is_strictly_concave_on_the_nonnegative_half_line :
    StrictConcaveOn ℝ (Ici 0) Real.tanh := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
    tanh_lipschitz.continuous.continuousOn
  simpa only [interior_Ici] using
    actual_tanh_derivative_strictly_decreases_on_positive_inputs

theorem actual_tanh_origin_secant_strictly_decreases_on_positive_inputs :
    StrictAntiOn (fun x : ℝ => Real.tanh x / x) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have h := actual_tanh_is_strictly_concave_on_the_nonnegative_half_line.secant_strict_mono
    (show (0:ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx0.le)
    (show y ∈ Ici 0 from hy0.le) (ne_of_gt hx0) (ne_of_gt hy0) hxy
  simpa only [Real.tanh_zero,sub_zero] using h

def sourceH (x : ℝ) : ℝ := Real.tanh x - x * (1-(Real.tanh x)^2)

theorem actual_source_h_has_the_printed_derivative (x : ℝ) :
    HasDerivAt sourceH (2*x*Real.tanh x*(1-(Real.tanh x)^2)) x := by
  have ht := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative x).1
  have h := ht.sub ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (ht.pow 2)))
  convert h using 1
  · funext z; rfl
  · simp only [Pi.sub_apply,Pi.pow_apply,id_eq,one_mul,zero_sub]
    norm_num only
    ring

theorem actual_source_h_is_positive_for_every_positive_input (x : ℝ) (hx : 0 < x) :
    0 < sourceH x := by
  have hmono : StrictMonoOn sourceH (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro z _
      exact (actual_source_h_has_the_printed_derivative z).continuousAt.continuousWithinAt
    · intro z hz
      have hz0 : 0 < z := by simpa only [interior_Ici,mem_Ioi] using hz
      rw [(actual_source_h_has_the_printed_derivative z).deriv]
      have ht : 0 < Real.tanh z := by
        have hs := (actual_tanh_chord_quotient_is_positive_and_at_most_one z 0
          (ne_of_gt hz0)).1
        simp only [Real.tanh_zero,sub_zero] at hs
        rcases div_pos_iff.mp hs with hs | hs
        · exact hs.1
        · linarith [hs.2]
      have hd := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative z).2.1
      positivity
  have h := hmono (show (0:ℝ) ∈ Ici 0 by simp) hx.le hx
  simpa only [sourceH,Real.tanh_zero,zero_mul,sub_zero] using h

theorem actual_origin_ratio_has_the_printed_negative_derivative
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.tanh z / z) (-sourceH x / x^2) x := by
  have ht := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative x).1
  convert ht.div (hasDerivAt_id x) hx using 1
  · funext point; rfl
  · simp only [id_eq,sourceH]; ring

theorem actual_origin_ratio_is_strictly_between_the_endpoint_derivative_and_one
    (radius : ℝ) (hr : 0 < radius) :
    1-(Real.tanh radius)^2 < Real.tanh radius/radius ∧
      Real.tanh radius/radius < 1 := by
  constructor
  · apply (lt_div_iff₀ hr).mpr
    have h := actual_source_h_is_positive_for_every_positive_input radius hr
    dsimp [sourceH] at h
    linarith
  · have h := actual_tanh_is_strictly_concave_on_the_nonnegative_half_line.slope_lt_of_hasDerivAt
      (show (0:ℝ) ∈ Ici 0 by simp) hr.le hr (tanh_derivative 0)
    simpa only [slope_def_field,Real.tanh_zero,Real.cosh_zero,sub_zero,one_pow,div_one] using h

theorem actual_origin_ratio_lower_bound_is_attained_and_greatest
    (radius : ℝ) (hr : 0 < radius) :
    IsGreatest {lower : ℝ | ∀ point : ℝ, point ≠ 0 → |point| ≤ radius →
      lower ≤ Real.tanh point / point} (Real.tanh radius/radius) := by
  refine ⟨?_,?_⟩
  · intro point hne hinside
    rw [actual_tanh_origin_secant_depends_only_on_absolute_input point]
    exact actual_tanh_origin_secant_is_antitone_on_positive_inputs (abs_pos.mpr hne) hr hinside
  · intro lower hlower
    exact hlower radius (ne_of_gt hr) (by simpa only [abs_of_pos hr] using le_refl radius)

theorem actual_origin_ratio_approaches_the_upper_endpoint_one_at_zero :
    Tendsto (fun x : ℝ => Real.tanh x/x) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h := (tanh_derivative 0).tendsto_slope
  convert h using 1
  · funext point; simp only [slope_def_field,Real.tanh_zero,sub_zero]
  · norm_num

theorem actual_chords_near_the_positive_endpoint_approach_the_lower_derivative_bound
    (radius : ℝ) :
    Tendsto (fun point : ℝ => (Real.tanh point-Real.tanh radius)/(point-radius))
      (nhdsWithin radius (Iio radius)) (nhds (1-(Real.tanh radius)^2)) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (actual_tanh_has_the_literal_strictly_positive_bounded_derivative radius).1).1
  convert h using 1
  funext point; exact (slope_def_field Real.tanh radius point).symm

theorem actual_chords_near_zero_approach_the_upper_derivative_bound :
    Tendsto (fun point : ℝ => (Real.tanh point-Real.tanh 0)/(point-0))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp (tanh_derivative 0)).2
  convert h using 1
  · funext point; exact (slope_def_field Real.tanh 0 point).symm
  · norm_num

end SafeLearning.CompleteModulesTanhSharpBounds
