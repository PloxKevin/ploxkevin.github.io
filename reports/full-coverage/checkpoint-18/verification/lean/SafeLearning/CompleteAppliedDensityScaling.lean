import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedDensityScaling
open MeasureTheory
open scoped ENNReal

variable {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]

theorem actual_measurable_equivalence_maps_the_weighted_measure
    (equiv : Alpha ≃ᵐ Beta) (measure : Measure Alpha) (weight : Alpha → ℝ≥0∞)
    (hweight : Measurable weight) :
    (measure.withDensity weight).map equiv =
      (measure.map equiv).withDensity (fun y => weight (equiv.symm y)) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest equiv.measurable,
    lintegral_withDensity_eq_lintegral_mul measure hweight
      (show Measurable (fun x => test (equiv x)) from htest.comp equiv.measurable),
    lintegral_withDensity_eq_lintegral_mul (measure.map equiv)
      (show Measurable (fun y => weight (equiv.symm y)) from
        hweight.comp equiv.symm.measurable) htest]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => weight (equiv.symm y)*test y) from
    (hweight.comp equiv.symm.measurable).mul htest) equiv.measurable]
  simp only [equiv.symm_apply_apply]

def actualDensityLaw (density : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (density x))

def actualScaledDensity (scale : ℝ) (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  density (x / scale) / |scale|

theorem actual_nonzero_rescaling_maps_the_true_density_law
    (density : ℝ → ℝ) (hmeasurable : Measurable density)
    (scale : ℝ) (hscale : scale ≠ 0) :
    (actualDensityLaw density).map (fun x => scale*x) =
      actualDensityLaw (actualScaledDensity scale density) := by
  let equiv : ℝ ≃ᵐ ℝ := (Homeomorph.smul (Units.mk0 scale hscale)).toMeasurableEquiv
  have he : (fun x : ℝ => scale*x) = equiv := by rfl
  rw [he,actualDensityLaw,
    actual_measurable_equivalence_maps_the_weighted_measure equiv volume _ hmeasurable.ennreal_ofReal]
  have hm : volume.map equiv = ENNReal.ofReal |scale⁻¹| • (volume : Measure ℝ) := by
    rw [←he]
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (volume : Measure ℝ) hscale)
  rw [hm,withDensity_smul_measure,←withDensity_smul _
    (show Measurable (fun y => ENNReal.ofReal (density (equiv.symm y))) from
      hmeasurable.ennreal_ofReal.comp equiv.symm.measurable)]
  congr 1
  funext x
  change ENNReal.ofReal |scale⁻¹| * ENNReal.ofReal (density (scale⁻¹*x)) =
    ENNReal.ofReal (density (x/scale) / |scale|)
  rw [←ENNReal.ofReal_mul (abs_nonneg _),abs_inv]
  congr 1
  have hx : scale⁻¹*x=x/scale := by rw [div_eq_mul_inv,mul_comm]
  simp only [hx,div_eq_mul_inv]
  ring

theorem actual_normalized_nonnegative_density_is_a_probability_law
    (density : ℝ → ℝ) (hnonnegative : ∀ x,0 ≤ density x)
    (hintegrable : Integrable density) (hmass : (∫ x,density x)=1) :
    IsProbabilityMeasure (actualDensityLaw density) := by
  constructor
  rw [actualDensityLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hintegrable (Filter.Eventually.of_forall hnonnegative),hmass]
  norm_num

def actualDifferentialEntropy (density : ℝ → ℝ) : ℝ :=
  -(∫ x,density x * Real.log (density x))

theorem actual_density_entropy_is_log_density_under_the_true_law
    (density : ℝ → ℝ) (hmeasurable : Measurable density)
    (hnonnegative : ∀ x,0 ≤ density x) :
    actualDifferentialEntropy density =
      -(∫ x,Real.log (density x) ∂actualDensityLaw density) := by
  unfold actualDifferentialEntropy actualDensityLaw
  rw [integral_withDensity_eq_integral_toReal_smul hmeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnonnegative _),smul_eq_mul]

theorem actual_rescaled_density_is_integrable_and_normalized
    (density : ℝ → ℝ) (hdensity : Integrable density)
    (hmass : (∫ x,density x)=1) (scale : ℝ) (hscale : scale ≠ 0) :
    Integrable (actualScaledDensity scale density) ∧
      (∫ x,actualScaledDensity scale density x)=1 := by
  refine ⟨(hdensity.comp_div hscale).div_const _,?_⟩
  simp only [actualScaledDensity,integral_div,Measure.integral_comp_div,smul_eq_mul,hmass,mul_one]
  exact div_self (abs_ne_zero.mpr hscale)

theorem actual_scaled_density_log_integrand (density : ℝ → ℝ)
    (scale : ℝ) (hscale : scale ≠ 0) (x : ℝ) :
    actualScaledDensity scale density x * Real.log (actualScaledDensity scale density x) =
      (density (x/scale)*Real.log (density (x/scale))-
        Real.log |scale| * density (x/scale)) / |scale| := by
  unfold actualScaledDensity
  by_cases hz : density (x/scale)=0
  · simp [hz]
  · rw [Real.log_div hz (abs_ne_zero.mpr hscale)]
    ring

theorem actual_rescaled_density_entropy_integrand_is_integrable
    (density : ℝ → ℝ) (hdensity : Integrable density)
    (hentropy : Integrable (fun x => density x * Real.log (density x)))
    (scale : ℝ) (hscale : scale ≠ 0) :
    Integrable (fun x => actualScaledDensity scale density x *
      Real.log (actualScaledDensity scale density x)) := by
  have h := ((hentropy.comp_div hscale).sub
    ((hdensity.comp_div hscale).const_mul (Real.log |scale|))).div_const |scale|
  simpa only [actual_scaled_density_log_integrand density scale hscale,Pi.sub_apply] using h

theorem actual_differential_entropy_rescaling (density : ℝ → ℝ)
    (hdensity : Integrable density)
    (hentropy : Integrable (fun x => density x * Real.log (density x)))
    (hmass : (∫ x,density x)=1) (scale : ℝ) (hscale : scale ≠ 0) :
    actualDifferentialEntropy (actualScaledDensity scale density) =
      actualDifferentialEntropy density + Real.log |scale| := by
  have hd := hdensity.comp_div hscale
  have hh := hentropy.comp_div hscale
  have he : (fun x => actualScaledDensity scale density x *
      Real.log (actualScaledDensity scale density x)) =
      (fun x => (density (x/scale)*Real.log (density (x/scale))-
        Real.log |scale| * density (x/scale)) / |scale|) := by
    funext x
    exact actual_scaled_density_log_integrand density scale hscale x
  unfold actualDifferentialEntropy
  rw [he,integral_div,integral_sub hh (hd.const_mul _),integral_const_mul,
    Measure.integral_comp_div (fun x => density x * Real.log (density x)) scale,
    Measure.integral_comp_div density scale,hmass]
  simp only [smul_eq_mul,mul_one]
  field_simp
  ring

end SafeLearning.CompleteAppliedDensityScaling
