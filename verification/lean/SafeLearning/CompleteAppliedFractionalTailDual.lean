import SafeLearning.CompleteFoundationsCVaRQuotients

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
namespace SafeLearning.CompleteAppliedFractionalTailDual
open CompleteFoundationsHingeExpectations CompleteFoundationsCVaRQuotients

def admissibleSelectors {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (mass : ℝ) : Set (Ω→ℝ) :=
  {selector | Measurable selector ∧ (∀omega,selector omega∈Icc (0:ℝ) 1) ∧
    (∫omega,selector omega ∂P)=mass}

def actualTailMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (loss selector : Ω→ℝ) (mass : ℝ) : ℝ := (∫omega,loss omega*selector omega ∂P)/mass

def actualWorstTailMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (loss : Ω→ℝ) (mass : ℝ) : ℝ :=
  sSup ((fun selector=>actualTailMean P loss selector mass) '' admissibleSelectors P mass)

theorem actual_bounded_selectors_and_selected_losses_are_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss selector : Ω→ℝ) (hi : Integrable loss P) (hm : Measurable selector)
    (hb : ∀omega,selector omega∈Icc (0:ℝ) 1) :
    Integrable selector P ∧ Integrable (fun omega=>loss omega*selector omega) P := by
  constructor
  · apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with omega
    rw [Real.norm_eq_abs,abs_of_nonneg (hb omega).1]
    exact (hb omega).2
  · apply hi.mono (hi.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    filter_upwards [] with omega
    change |loss omega*selector omega|≤|loss omega|
    simp only [abs_mul,abs_of_nonneg (hb omega).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb omega).2

theorem actual_pointwise_hinge_bounds_every_fractional_selected_loss
    (value threshold selector : ℝ) (hs : selector∈Icc (0:ℝ) 1) :
    value*selector≤hinge value threshold+threshold*selector := by
  unfold hinge
  by_cases hv : threshold≤value
  · rw [max_eq_left (sub_nonneg.mpr hv)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hs.2)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hv))]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hv)) hs.1]

theorem actual_every_admissible_fractional_tail_is_bounded_by_every_RU_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hi : Integrable loss P) (alpha threshold : ℝ) (ha : alpha<1)
    (selector : Ω→ℝ) (hs : selector∈admissibleSelectors P (1-alpha)) :
    actualTailMean P loss selector (1-alpha)≤actualRUObjective P loss alpha threshold := by
  obtain ⟨hsm,hsb,hsmass⟩ := hs
  have hsi := actual_bounded_selectors_and_selected_losses_are_integrable loss selector hi hsm hsb
  have hh := actual_integrable_random_loss_has_integrable_hinge_at_every_threshold loss hi threshold
  have hb := integral_mono hsi.2 (hh.add (hsi.1.const_mul threshold))
    (fun omega=>actual_pointwise_hinge_bounds_every_fractional_selected_loss (loss omega) threshold (selector omega) (hsb omega))
  change (∫omega,loss omega*selector omega ∂P)≤
    (∫omega,hinge (loss omega) threshold+threshold*selector omega ∂P) at hb
  rw [integral_add hh (hsi.1.const_mul threshold),integral_const_mul,hsmass] at hb
  unfold actualTailMean actualRUObjective
  apply (div_le_iff₀ (sub_pos.mpr ha)).mpr
  have he : (threshold+1/(1-alpha)*(∫omega,hinge (loss omega) threshold ∂P))*(1-alpha)=
      (∫omega,hinge (loss omega) threshold ∂P)+threshold*(1-alpha) := by
    field_simp [(sub_pos.mpr ha).ne']
    ring
  rw [he]
  exact hb

theorem actual_threshold_tail_selector_has_exact_hinge_identity
    (value threshold selector : ℝ) (_hs : selector∈Icc (0:ℝ) 1)
    (habove : threshold<value→selector=1) (hbelow : value<threshold→selector=0) :
    value*selector=hinge value threshold+threshold*selector := by
  rcases lt_trichotomy value threshold with h | h | h
  · rw [hbelow h]
    simp [hinge,max_eq_right (sub_nonpos.mpr h.le)]
  · rw [h]
    simp [hinge]
  · rw [habove h]
    simp [hinge,max_eq_left (sub_nonneg.mpr h.le)]

theorem actual_mass_matched_threshold_selector_attains_the_RU_value
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hi : Integrable loss P) (alpha threshold : ℝ) (ha : alpha<1)
    (selector : Ω→ℝ) (hs : selector∈admissibleSelectors P (1-alpha))
    (habove : ∀omega,threshold<loss omega→selector omega=1)
    (hbelow : ∀omega,loss omega<threshold→selector omega=0) :
    actualTailMean P loss selector (1-alpha)=actualRUObjective P loss alpha threshold := by
  obtain ⟨hsm,hsb,hsmass⟩ := hs
  have hsi := actual_bounded_selectors_and_selected_losses_are_integrable loss selector hi hsm hsb
  have hh := actual_integrable_random_loss_has_integrable_hinge_at_every_threshold loss hi threshold
  have he : (fun omega=>loss omega*selector omega)=
      (fun omega=>hinge (loss omega) threshold+threshold*selector omega) := by
    funext omega
    exact actual_threshold_tail_selector_has_exact_hinge_identity (loss omega) threshold (selector omega)
      (hsb omega) (habove omega) (hbelow omega)
  unfold actualTailMean
  rw [he,integral_add hh (hsi.1.const_mul threshold),integral_const_mul,hsmass]
  unfold actualRUObjective
  field_simp [(sub_pos.mpr ha).ne']
  ring

theorem actual_mass_matched_threshold_selector_is_greatest_tail_and_least_RU_objective
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hi : Integrable loss P) (alpha threshold : ℝ) (ha : alpha<1)
    (selector : Ω→ℝ) (hs : selector∈admissibleSelectors P (1-alpha))
    (habove : ∀omega,threshold<loss omega→selector omega=1)
    (hbelow : ∀omega,loss omega<threshold→selector omega=0) :
    IsGreatest ((fun other=>actualTailMean P loss other (1-alpha)) '' admissibleSelectors P (1-alpha))
      (actualTailMean P loss selector (1-alpha)) ∧
    IsLeast (Set.range (actualRUObjective P loss alpha)) (actualRUObjective P loss alpha threshold) ∧
    actualWorstTailMean P loss (1-alpha)=actualRUObjective P loss alpha threshold := by
  have he := actual_mass_matched_threshold_selector_attains_the_RU_value loss hi alpha threshold ha selector hs habove hbelow
  have hg : IsGreatest ((fun other=>actualTailMean P loss other (1-alpha)) '' admissibleSelectors P (1-alpha))
      (actualTailMean P loss selector (1-alpha)) := by
    refine ⟨⟨selector,hs,rfl⟩,?_⟩
    rintro value ⟨other,ho,rfl⟩
    rw [he]
    exact actual_every_admissible_fractional_tail_is_bounded_by_every_RU_threshold loss hi alpha threshold ha other ho
  refine ⟨hg,?_,?_⟩
  · refine ⟨⟨threshold,rfl⟩,?_⟩
    rintro value ⟨other,rfl⟩
    rw [←he]
    exact actual_every_admissible_fractional_tail_is_bounded_by_every_RU_threshold loss hi alpha other ha selector hs
  · exact hg.csSup_eq.trans he

end SafeLearning.CompleteAppliedFractionalTailDual
