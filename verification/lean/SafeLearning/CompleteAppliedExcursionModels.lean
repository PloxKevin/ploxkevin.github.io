import SafeLearning.CompleteAppliedSupportConsequences
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
namespace SafeLearning.CompleteAppliedExcursionModels
open SafeLearning.CompleteAppliedSupportConsequences SafeLearning.CompleteAppliedUniformDefinitions

theorem actual_excursion_is_continuous : Continuous actualExcursion :=
  continuous_id.max continuous_const

def actualSignedLaw : Measure ℝ := actualUniformLaw (-1) 1
instance : IsProbabilityMeasure actualSignedLaw :=
  actual_uniform_law_is_a_probability_measure (-1) 1 (by norm_num)
def actualExcursionLaw : Measure ℝ := actualSignedLaw.map actualExcursion
instance : IsProbabilityMeasure actualExcursionLaw := by
  unfold actualExcursionLaw
  infer_instance

theorem actual_excursion_lower_event_is_the_original_uniform_lower_event
    (level : ℝ) (hn : 0≤level) :
    actualExcursion ⁻¹' Iic level=Iic level := by
  ext input
  simp only [mem_preimage,mem_Iic,actualExcursion,max_le_iff,and_iff_left hn]

theorem actual_excursion_cdf_is_the_printed_linear_expression
    (level : ℝ) (hn : 0≤level) (hu : level≤1) :
    cdf actualExcursionLaw level=(1+level)/2 := by
  rw [cdf_eq_real,measureReal_def,actualExcursionLaw,
    Measure.map_apply actual_excursion_is_continuous.measurable measurableSet_Iic,
    actual_excursion_lower_event_is_the_original_uniform_lower_event level hn]
  rw [actualSignedLaw,actual_uniform_probability_is_length_ratio (-1) 1 (by norm_num)
    (Iic level) measurableSet_Iic]
  have he : Iic level ∩ Icc (-1:ℝ) 1=Icc (-1) level := by
    ext input
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hle,hlo,_⟩;exact ⟨hlo,hle⟩
    · rintro ⟨hlo,hle⟩;exact ⟨hle,hlo,hle.trans hu⟩
  rw [he,Real.volume_Icc,ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal (by linarith : 0≤level-(-1))]
  norm_num
  ring

theorem actual_excursion_cdf_below_zero_is_zero (level : ℝ) (hn : level<0) :
    cdf actualExcursionLaw level=0 := by
  rw [cdf_eq_real,measureReal_def,actualExcursionLaw,
    Measure.map_apply actual_excursion_is_continuous.measurable measurableSet_Iic]
  have he : actualExcursion ⁻¹' Iic level=∅ := by
    ext input
    simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false,not_le]
    exact hn.trans_le (le_max_right input 0)
  rw [he,measure_empty,ENNReal.toReal_zero]

theorem actual_excursion_has_an_atom_of_exactly_one_half_at_zero :
    actualExcursionLaw {0}=1/2 := by
  have he : actualExcursion ⁻¹' ({0}:Set ℝ)=Iic 0 := by
    ext input
    simp only [mem_preimage,mem_singleton_iff,mem_Iic,actualExcursion]
    exact max_eq_right_iff
  rw [actualExcursionLaw,Measure.map_apply
    actual_excursion_is_continuous.measurable (measurableSet_singleton 0),he,
    actualSignedLaw,actual_uniform_probability_is_length_ratio (-1) 1 (by norm_num)
      (Iic 0) measurableSet_Iic]
  have hx : Iic (0:ℝ) ∩ Icc (-1) 1=Icc (-1) 0 := by
    ext input
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hle,hlo,_⟩;exact ⟨hlo,hle⟩
    · rintro ⟨hlo,hle⟩;exact ⟨hle,hlo,by linarith⟩
  rw [hx,Real.volume_Icc]
  norm_num

theorem actual_uniform_positive_part_integral_is_one_quarter :
    (∫ input,actualExcursion input ∂actualSignedLaw)=1/4 := by
  have hc : Continuous actualExcursion := continuous_id.max continuous_const
  have hleft : (∫ input in (-1:ℝ)..0,actualExcursion input)=0 := by
    have he : (∫ input in (-1:ℝ)..0,actualExcursion input)=∫ input in (-1:ℝ)..0,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro input hi
      rw [uIcc_of_le (by norm_num : (-1:ℝ)≤0)] at hi
      exact max_eq_right hi.2
    rw [he];simp
  have hright : (∫ input in (0:ℝ)..1,actualExcursion input)=1/2 := by
    have he : (∫ input in (0:ℝ)..1,actualExcursion input)=∫ input in (0:ℝ)..1,input := by
      apply intervalIntegral.integral_congr
      intro input hi
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hi
      exact max_eq_left hi.1
    rw [he,integral_id];norm_num
  rw [actualSignedLaw,actual_uniform_law_is_the_true_normalized_restriction (-1) 1 (by norm_num),
    integral_smul_measure,smul_eq_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1),
    hleft,hright]
  norm_num

theorem actual_excursion_integrability_and_true_law_expectation_are_derived :
    Integrable actualExcursion actualSignedLaw ∧
      Integrable (fun input : ℝ=>input) actualExcursionLaw ∧
      (∫ input : ℝ,input ∂actualExcursionLaw)=1/4 := by
  have hbounded : ∀ᵐ input ∂actualSignedLaw, |actualExcursion input|≤1 := by
    filter_upwards [actualSignedLaw.support_mem_ae] with input hi
    rw [actualSignedLaw,SafeLearning.CompleteAppliedMeasureSupport.actual_uniform_interval_support_is_the_exact_closed_interval (-1) 1 (by norm_num)] at hi
    change |max input 0|≤1
    rw [abs_of_nonneg (le_max_right input 0)]
    exact max_le hi.2 (by norm_num)
  have hc : Continuous actualExcursion := continuous_id.max continuous_const
  have hint : Integrable actualExcursion actualSignedLaw :=
    (integrable_const (1:ℝ)).mono' hc.aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hbounded)
  refine ⟨hint,?_,?_⟩
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable hc.measurable.aemeasurable).mpr hint
  · change (∫ input,id input ∂actualSignedLaw.map actualExcursion)=1/4
    rw [integral_map hc.measurable.aemeasurable measurable_id.aestronglyMeasurable]
    exact actual_uniform_positive_part_integral_is_one_quarter

end SafeLearning.CompleteAppliedExcursionModels
