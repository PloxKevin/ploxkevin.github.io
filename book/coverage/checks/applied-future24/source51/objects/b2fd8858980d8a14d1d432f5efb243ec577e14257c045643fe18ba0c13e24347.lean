import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsHingeExpectations

def hinge (value threshold : ℝ) : ℝ := max (value - threshold) 0
def hingeQuotient (value center threshold : ℝ) : ℝ :=
  (hinge value threshold - hinge value center) / (threshold - center)

theorem actual_hinge_difference_quotients_are_uniformly_bounded_by_one
    (value center threshold : ℝ) : |hingeQuotient value center threshold| ≤ 1 := by
  have hb := abs_max_sub_max_le_max (value - threshold) 0 (value - center) 0
  have heq : (value - threshold) - (value - center) = -(threshold - center) := by ring
  simp only [sub_zero, abs_zero] at hb
  rw [heq, abs_neg, max_eq_left (abs_nonneg (threshold - center))] at hb
  change |hinge value threshold - hinge value center| ≤ |threshold - center| at hb
  unfold hingeQuotient
  rw [abs_div]
  by_cases he : threshold = center
  · simp [he]
  · exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr he))).mpr hb

theorem actual_every_point_right_hinge_quotient_limit_retains_the_strict_tail
    (value center : ℝ) :
    Tendsto (fun threshold => hingeQuotient value center threshold) (𝓝[>] center)
      (𝓝 (if center < value then (-1 : ℝ) else 0)) := by
  by_cases h : center < value
  · simp only [ite_eq_left h]
    apply tendsto_const_nhds.congr'
    have hi0 : ∀ᶠ threshold in 𝓝 center, threshold < value := Iio_mem_nhds h
    have hi : ∀ᶠ threshold in 𝓝[>] center, threshold < value :=
      hi0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hi, self_mem_nhdsWithin] with threshold ht hn
    change center < threshold at hn
    unfold hingeQuotient hinge
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp [(sub_pos.mpr hn).ne']
    ring
  · simp only [ite_eq_right h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with threshold hn
    change center < threshold at hn
    have hc : value ≤ center := le_of_not_gt h
    simp [hingeQuotient, hinge, max_eq_right (by linarith : value - threshold ≤ 0),
      max_eq_right (by linarith : value - center ≤ 0)]

theorem actual_every_point_left_hinge_quotient_limit_retains_the_nonstrict_tail
    (value center : ℝ) :
    Tendsto (fun threshold => hingeQuotient value center threshold) (𝓝[<] center)
      (𝓝 (if center ≤ value then (-1 : ℝ) else 0)) := by
  by_cases h : center ≤ value
  · simp only [ite_eq_left h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with threshold hn
    change threshold < center at hn
    unfold hingeQuotient hinge
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp [sub_ne_zero.mpr (ne_of_lt hn)]
    ring
  · simp only [ite_eq_right h]
    apply tendsto_const_nhds.congr'
    have hv : value < center := lt_of_not_ge h
    have hi0 : ∀ᶠ threshold in 𝓝 center, value < threshold := Ioi_mem_nhds hv
    have hi : ∀ᶠ threshold in 𝓝[<] center, value < threshold :=
      hi0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hi] with threshold ht
    simp [hingeQuotient, hinge, max_eq_right (by linarith : value - threshold ≤ 0),
      max_eq_right (by linarith : value - center ≤ 0)]

theorem actual_integrable_random_loss_has_integrable_hinge_at_every_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω → ℝ) (h : Integrable loss P) (threshold : ℝ) :
    Integrable (fun omega => hinge (loss omega) threshold) P := by
  exact (h.sub (integrable_const threshold)).sup (integrable_const 0)

theorem actual_bounded_convergence_moves_both_one_sided_hinge_quotients_through_expectation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω → ℝ) (hm : Measurable loss) (hi : Integrable loss P) (center : ℝ) :
    Tendsto (fun threshold =>
      ((∫ omega, hinge (loss omega) threshold ∂P) -
        (∫ omega, hinge (loss omega) center ∂P)) / (threshold - center))
      (𝓝[>] center) (𝓝 (-P.real {omega | center < loss omega})) ∧
    Tendsto (fun threshold =>
      ((∫ omega, hinge (loss omega) threshold ∂P) -
        (∫ omega, hinge (loss omega) center ∂P)) / (threshold - center))
      (𝓝[<] center) (𝓝 (-P.real {omega | center ≤ loss omega})) := by
  have hmeas (threshold : ℝ) :
      AEStronglyMeasurable (fun omega => hingeQuotient (loss omega) center threshold) P := by
    unfold hingeQuotient hinge
    exact ((((hm.sub measurable_const).max measurable_const).sub
      ((hm.sub measurable_const).max measurable_const)).div_const _).aestronglyMeasurable
  have hbound (threshold : ℝ) : ∀ᵐ omega ∂P,
      ‖hingeQuotient (loss omega) center threshold‖ ≤ (1 : ℝ) :=
    Eventually.of_forall (fun omega => by
      simpa only [Real.norm_eq_abs] using
        actual_hinge_difference_quotients_are_uniformly_bounded_by_one (loss omega) center threshold)
  have hright := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (integrable_const 1)
    (Eventually.of_forall (fun omega =>
      actual_every_point_right_hinge_quotient_limit_retains_the_strict_tail (loss omega) center))
  have hleft := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (integrable_const 1)
    (Eventually.of_forall (fun omega =>
      actual_every_point_left_hinge_quotient_limit_retains_the_nonstrict_tail (loss omega) center))
  have hformula (threshold : ℝ) :
      (∫ omega, hingeQuotient (loss omega) center threshold ∂P) =
      ((∫ omega, hinge (loss omega) threshold ∂P) -
        (∫ omega, hinge (loss omega) center ∂P)) / (threshold - center) := by
    unfold hingeQuotient
    rw [integral_div, integral_sub
      (actual_integrable_random_loss_has_integrable_hinge_at_every_threshold loss hi threshold)
      (actual_integrable_random_loss_has_integrable_hinge_at_every_threshold loss hi center)]
  have hrightIntegral :
      (∫ omega, (if center < loss omega then (-1 : ℝ) else 0) ∂P) =
        -P.real {omega | center < loss omega} := by
    have hs : MeasurableSet {omega | center < loss omega} := measurableSet_lt measurable_const hm
    calc
      _ = (∫ omega, ({omega | center < loss omega}).indicator
          (fun _ : Ω => (-1 : ℝ)) omega ∂P) := by rfl
      _ = _ := by simpa only [smul_eq_mul, mul_neg_one] using integral_indicator_const (-1 : ℝ) hs
  have hleftIntegral :
      (∫ omega, (if center ≤ loss omega then (-1 : ℝ) else 0) ∂P) =
        -P.real {omega | center ≤ loss omega} := by
    have hs : MeasurableSet {omega | center ≤ loss omega} := measurableSet_le measurable_const hm
    calc
      _ = (∫ omega, ({omega | center ≤ loss omega}).indicator
          (fun _ : Ω => (-1 : ℝ)) omega ∂P) := by rfl
      _ = _ := by simpa only [smul_eq_mul, mul_neg_one] using integral_indicator_const (-1 : ℝ) hs
  simpa only [hformula, hrightIntegral, hleftIntegral] using And.intro hright hleft

end SafeLearning.CompleteFoundationsHingeExpectations
