import SafeLearning.CompleteAppliedExcursionModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedExcursionConsequences
open SafeLearning.CompleteAppliedExcursionModels SafeLearning.CompleteAppliedSupportConsequences

theorem actual_excursion_law_has_no_negative_mass :
    actualExcursionLaw (Iio 0)=0 := by
  rw [actualExcursionLaw,Measure.map_apply actual_excursion_is_continuous.measurable measurableSet_Iio]
  have he : actualExcursion ⁻¹' Iio 0=∅ := by
    ext input
    simp only [mem_preimage,mem_Iio,mem_empty_iff_false,iff_false,not_lt]
    exact le_max_right input 0
  rw [he,measure_empty]

theorem actual_excursion_law_is_neither_nondegenerate_nor_degenerate_gaussian
    (mean : ℝ) (variance : NNReal) : actualExcursionLaw≠gaussianReal mean variance := by
  intro he
  have ha := actual_excursion_has_an_atom_of_exactly_one_half_at_zero
  rw [he] at ha
  by_cases hv : variance=0
  · subst variance
    rw [gaussianReal_zero_var] at ha
    by_cases hm : mean=0
    · subst mean
      have hd : (Measure.dirac (0:ℝ)) {0}=1 := by simp
      rw [hd] at ha
      have hh := congrArg ENNReal.toReal ha
      norm_num at hh
    · have hd : (Measure.dirac mean) {0}=0 := by
        rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]
        simp [hm]
      rw [hd] at ha
      have hh := congrArg ENNReal.toReal ha
      norm_num at hh
  · let : NullSingletonClass (gaussianReal mean variance) := nullSingletonClass_gaussianReal hv
    rw [measure_singleton] at ha
    have hh := congrArg ENNReal.toReal ha
    norm_num at hh

end SafeLearning.CompleteAppliedExcursionConsequences
