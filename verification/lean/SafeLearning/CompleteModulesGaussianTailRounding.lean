import SafeLearning.CompleteModulesGaussianErfcTail
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace SafeLearning.CompleteModulesGaussianTailRounding
open CompleteAppliedGaussianCDF CompleteModulesGaussianErfcTail

/-! A real-valued model of nearest rounding to the nonnegative binary64
values in [0,1]. The exponent and fraction fields are finite; exponent zero
uses subnormal decoding, and exponent 1023 is the binade starting at one.
Filtering at one excludes the rest of that binade. Signed zero is identified
with real zero. All results below avoid ties, so no tie-breaking assumption
is needed. This is a value/rounding model, not a claim about a particular
implementation of `erfc`, `exp`, or a language's floating-point primitives. -/

abbrev Encoding := Fin 1024 × Fin (2^52)

def decode (bits : Encoding) : ℝ :=
  if bits.1.val = 0 then (bits.2.val : ℝ) * (2:ℝ)^(-1074:ℤ)
  else ((2:ℝ)^52 + bits.2.val) * (2:ℝ)^((bits.1.val:ℤ)-1075)

def unitValues : Set ℝ := Set.range decode ∩ Icc 0 1
def minPositive : ℝ := (2:ℝ)^(-1074:ℤ)
def gapBelowOne : ℝ := (2:ℝ)^(-53:ℤ)

theorem actual_binary64_unit_value_set_is_finite : unitValues.Finite :=
  (Set.finite_range decode).inter_of_left _

theorem actual_zero_and_one_are_representable : 0 ∈ unitValues ∧ 1 ∈ unitValues := by
  constructor
  · refine ⟨⟨(⟨0, by norm_num⟩, ⟨0, by norm_num⟩), ?_⟩, by norm_num⟩
    norm_num [decode]
  · refine ⟨⟨(⟨1023, by norm_num⟩, ⟨0, by norm_num⟩), ?_⟩, by norm_num⟩
    norm_num [decode]

theorem actual_representable_positive_values_have_a_subnormal_floor
    (y : ℝ) (hy : y ∈ unitValues) (hp : 0 < y) : minPositive ≤ y := by
  rcases hy.1 with ⟨⟨e, f⟩, rfl⟩
  by_cases he : e.val = 0
  · have hf : 1 ≤ f.val := by
      by_contra h
      have hz : f.val = 0 := by omega
      simp [decode, he, hz] at hp
    have hfr : (1:ℝ) ≤ f.val := by exact_mod_cast hf
    simpa [decode, he, minPositive] using
      (mul_le_mul_of_nonneg_right hfr (le_of_lt (zpow_pos (by norm_num : (0:ℝ)<2) (-1074))))
  · have hexp : (-1074:ℤ) ≤ (e.val:ℤ)-1075 := by omega
    have hscale := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hexp
    have hm : (1:ℝ) ≤ (2:ℝ)^52 + f.val := by
      have hfr : (0:ℝ) ≤ f.val := by positivity
      norm_num
      linarith
    have hnonneg : 0 ≤ (2:ℝ)^((e.val:ℤ)-1075) := le_of_lt (zpow_pos (by norm_num) _)
    simpa [decode, he, minPositive] using
      hscale.trans (by simpa using mul_le_mul_of_nonneg_right hm hnonneg)

theorem actual_representable_values_below_one_have_a_gap
    (y : ℝ) (hy : y ∈ unitValues) (hlt : y < 1) : y ≤ 1-gapBelowOne := by
  rcases hy.1 with ⟨⟨e, f⟩, rfl⟩
  have hf : (f.val:ℝ) ≤ 4503599627370495 := by
    have h : f.val ≤ 4503599627370495 := by have := f.isLt; norm_num at this; omega
    exact_mod_cast h
  by_cases he : e.val = 0
  · have hscale : (2:ℝ)^(-1074:ℤ) ≤ (2:ℝ)^(-53:ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hscale (show (0:ℝ) ≤ f.val by positivity)
    have hb := mul_le_mul_of_nonneg_right hf (le_of_lt (zpow_pos (by norm_num : (0:ℝ)<2) (-53)))
    simp only [decode, he, ite_true]
    exact (hm.trans hb).trans (by norm_num [gapBelowOne])
  · by_cases ht : e.val = 1023
    · have hfzero : f.val = 0 := by
        have h := (show (0:ℝ) ≤ f.val by positivity)
        norm_num [decode, he, ht] at hlt
        nlinarith
      norm_num [decode, he, ht, hfzero] at hlt
    · have hexp : (e.val:ℤ)-1075 ≤ (-53:ℤ) := by have := e.isLt; omega
      have hscale := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hexp
      have hm := mul_le_mul_of_nonneg_left hscale (show (0:ℝ) ≤ (2:ℝ)^52+f.val by positivity)
      have hb := mul_le_mul_of_nonneg_right hf (le_of_lt (zpow_pos (by norm_num : (0:ℝ)<2) (-53)))
      simp only [decode, he, ite_false]
      have hnum : ((2:ℝ)^52 + f.val) * (2:ℝ)^(-53:ℤ) ≤ 1-gapBelowOne := by
        norm_num [gapBelowOne] at hb ⊢
        linarith
      exact hm.trans hnum

theorem actual_nearest_representable_value_exists (x : ℝ) :
    ∃ r ∈ unitValues, ∀ y ∈ unitValues, |x-r| ≤ |x-y| :=
  Set.exists_min_image unitValues (fun y => |x-y|)
    actual_binary64_unit_value_set_is_finite ⟨0, actual_zero_and_one_are_representable.1⟩

def roundUnit (x : ℝ) : ℝ := (actual_nearest_representable_value_exists x).choose

theorem actual_rounding_chooses_a_nearest_representable_value (x : ℝ) :
    roundUnit x ∈ unitValues ∧ ∀ y ∈ unitValues, |x-roundUnit x| ≤ |x-y| :=
  (actual_nearest_representable_value_exists x).choose_spec

theorem actual_representable_values_are_fixed_by_rounding (x : ℝ) (hx : x ∈ unitValues) :
    roundUnit x = x := by
  have h := (actual_rounding_chooses_a_nearest_representable_value x).2 x hx
  simp only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] at h
  exact h.symm

theorem actual_rounding_near_one_is_one (x : ℝ)
    (hx : 1-gapBelowOne/2 < x) (hx1 : x ≤ 1) : roundUnit x = 1 := by
  have hr := actual_rounding_chooses_a_nearest_representable_value x
  by_contra hne
  have hlt : roundUnit x < 1 := lt_of_le_of_ne hr.1.2.2 hne
  have hgap := actual_representable_values_below_one_have_a_gap _ hr.1 hlt
  have hg : 0 < gapBelowOne := zpow_pos (by norm_num) _
  have hxr : 0 ≤ x-roundUnit x := by linarith
  have hnear := hr.2 1 actual_zero_and_one_are_representable.2
  rw [abs_of_nonneg hxr, abs_of_nonpos (by linarith : x-1 ≤ 0)] at hnear
  linarith

theorem actual_rounding_below_half_the_subnormal_floor_is_zero (x : ℝ)
    (hx : 0 ≤ x) (hsmall : x < minPositive/2) : roundUnit x = 0 := by
  have hr := actual_rounding_chooses_a_nearest_representable_value x
  by_contra hne
  have hp : 0 < roundUnit x := lt_of_le_of_ne hr.1.2.1 (Ne.symm hne)
  have hfloor := actual_representable_positive_values_have_a_subnormal_floor _ hr.1 hp
  have hsmallr : x-roundUnit x ≤ 0 := by linarith
  have hnear := hr.2 0 actual_zero_and_one_are_representable.1
  rw [abs_of_nonpos hsmallr, sub_zero, abs_of_nonneg hx] at hnear
  linarith

theorem actual_smallest_positive_value_is_representable : minPositive ∈ unitValues := by
  refine ⟨⟨(⟨0, by norm_num⟩, ⟨1, by norm_num⟩), ?_⟩, ?_⟩
  · norm_num [decode, minPositive]
  · refine ⟨le_of_lt (zpow_pos (by norm_num) _), ?_⟩
    simpa [minPositive] using
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show (-1074:ℤ) ≤ 0 by norm_num))

theorem actual_rounding_above_half_the_subnormal_floor_is_positive (x : ℝ)
    (hx : minPositive/2 < x) : 0 < roundUnit x := by
  have hr := actual_rounding_chooses_a_nearest_representable_value x
  have hp : 0 < minPositive := zpow_pos (by norm_num) _
  apply lt_of_le_of_ne hr.1.2.1
  intro hz
  have hnear := hr.2 minPositive actual_smallest_positive_value_is_representable
  rw [← hz, sub_zero, abs_of_nonneg (by linarith : 0 ≤ x)] at hnear
  have hcloser : |x-minPositive| < x := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

def cdfSubtraction (z : ℝ) : ℝ := roundUnit (1-roundUnit (standardCDF z))
def directTail (z : ℝ) : ℝ := roundUnit (upperTail z)

theorem actual_gaussian_upper_tail_tends_to_zero :
    Tendsto upperTail atTop (𝓝 0) := by
  have hc : Tendsto standardCDF atTop (𝓝 1) := by
    have he : (fun x : ℝ => cdf (gaussianReal 0 1) x) = standardCDF := by
      funext x
      exact cdf_eq_real (gaussianReal 0 1) x
    rw [← he]
    exact tendsto_cdf_atTop (gaussianReal 0 1)
  have he : upperTail = fun z => 1-standardCDF z := by
    funext z
    exact (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral z).1
  rw [he]
  have hs : Tendsto (fun z => (1:ℝ)-standardCDF z) atTop (𝓝 ((1:ℝ)-1)) :=
    tendsto_const_nhds.sub hc
  simpa using hs

theorem actual_small_positive_gaussian_tails_can_be_lost_by_cdf_subtraction (z : ℝ)
    (hsmall : upperTail z < gapBelowOne/2) :
    roundUnit (standardCDF z) = 1 ∧ cdfSubtraction z = 0 ∧ 0 < upperTail z := by
  have hp := actual_gaussian_upper_tail_is_positive_at_every_finite_threshold z
  have hc := (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral z).1
  have hr : roundUnit (standardCDF z) = 1 :=
    actual_rounding_near_one_is_one _ (by linarith) (by linarith)
  refine ⟨hr, ?_, hp⟩
  simp only [cdfSubtraction, hr, sub_self]
  exact actual_representable_values_are_fixed_by_rounding 0 actual_zero_and_one_are_representable.1

theorem actual_finite_gaussian_thresholds_eventually_produce_false_zero_cdf_subtractions :
    ∃ R : ℝ, ∀ z : ℝ, R ≤ z →
      0 < upperTail z ∧ roundUnit (standardCDF z) = 1 ∧ cdfSubtraction z = 0 := by
  have hg : 0 < gapBelowOne/2 := by unfold gapBelowOne; positivity
  have he := actual_gaussian_upper_tail_tends_to_zero.eventually (gt_mem_nhds hg)
  rcases eventually_atTop.1 he with ⟨R, hR⟩
  refine ⟨R, fun z hz => ?_⟩
  have h := actual_small_positive_gaussian_tails_can_be_lost_by_cdf_subtraction z (hR z hz)
  exact ⟨h.2.2, h.1, h.2.1⟩

theorem actual_finite_gaussian_thresholds_eventually_underflow_even_with_direct_tails :
    ∃ R : ℝ, ∀ z : ℝ, R ≤ z →
      0 < upperTail z ∧ directTail z = 0 ∧
        roundUnit ((1/2:ℝ)*erfc (z/Real.sqrt 2)) = 0 := by
  have hp : 0 < minPositive/2 := by unfold minPositive; positivity
  have he := actual_gaussian_upper_tail_tends_to_zero.eventually (gt_mem_nhds hp)
  rcases eventually_atTop.1 he with ⟨R, hR⟩
  refine ⟨R, fun z hz => ?_⟩
  have hpos := actual_gaussian_upper_tail_is_positive_at_every_finite_threshold z
  have hr := actual_rounding_below_half_the_subnormal_floor_is_zero _ hpos.le (hR z hz)
  have herfc := (actual_density_change_of_variable_gives_the_complementary_error_function z).2
  exact ⟨hpos, hr, by rwa [← herfc]⟩

theorem actual_gaussian_tail_is_continuous_on_nonnegative_thresholds :
    ContinuousOn upperTail (Ici 0) := by
  have hi : Integrable (fun x : ℝ => Real.exp (-x^2/2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2) using 1
    funext x
    congr 1
    ring
  have hcont := hi.integrableOn.continuousOn_Ici_primitive_Ioi (a₀ := 0)
  have he : upperTail = fun z =>
      (Real.sqrt (2*Real.pi))⁻¹*(∫x in Ioi z, Real.exp (-x^2/2)) := by
    funext z
    exact (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral z).2
  rw [he]
  exact continuousOn_const.mul hcont

theorem actual_every_small_positive_tail_value_occurs_at_a_finite_threshold
    (q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1/2) :
    ∃ z : ℝ, 0 ≤ z ∧ upperTail z = q := by
  have he := actual_gaussian_upper_tail_tends_to_zero.eventually (gt_mem_nhds hq)
  rcases (he.and (eventually_ge_atTop (0:ℝ))).exists with ⟨R, hsmall, hR⟩
  have hcont : ContinuousOn upperTail (Icc 0 R) :=
    actual_gaussian_tail_is_continuous_on_nonnegative_thresholds.mono Icc_subset_Ici_self
  have hqmem : q ∈ Icc (upperTail R) (upperTail 0) := by
    rw [actual_zero_tail_has_half_mass_and_erfc_zero_is_one.1]
    exact ⟨hsmall.le, hqhalf⟩
  rcases intermediate_value_Icc' hR hcont hqmem with ⟨z, hz, heq⟩
  exact ⟨z, hz.1, heq⟩

theorem actual_direct_tail_can_retain_a_positive_value_lost_by_cdf_subtraction :
    ∃ z : ℝ, 0 ≤ z ∧ upperTail z = (2:ℝ)^(-60:ℤ) ∧
      roundUnit (standardCDF z) = 1 ∧ cdfSubtraction z = 0 ∧
      directTail z = (2:ℝ)^(-60:ℤ) ∧ 0 < directTail z := by
  have hrep : (2:ℝ)^(-60:ℤ) ∈ unitValues := by
    refine ⟨⟨(⟨963, by norm_num⟩, ⟨0, by norm_num⟩), ?_⟩, by norm_num⟩
    norm_num [decode]
  rcases actual_every_small_positive_tail_value_occurs_at_a_finite_threshold
      ((2:ℝ)^(-60:ℤ)) (by positivity) (by norm_num) with ⟨z, hz, htail⟩
  have hc := actual_small_positive_gaussian_tails_can_be_lost_by_cdf_subtraction z
    (by rw [htail]; norm_num [gapBelowOne])
  have hd : directTail z = (2:ℝ)^(-60:ℤ) := by
    rw [directTail, htail]
    exact actual_representable_values_are_fixed_by_rounding _ hrep
  exact ⟨z, hz, htail, hc.1, hc.2.1, hd, by rw [hd]; positivity⟩

end SafeLearning.CompleteModulesGaussianTailRounding
