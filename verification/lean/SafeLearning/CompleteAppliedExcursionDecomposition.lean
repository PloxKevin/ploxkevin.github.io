import SafeLearning.CompleteAppliedExcursionModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open Classical
namespace SafeLearning.CompleteAppliedExcursionDecomposition
open SafeLearning.CompleteAppliedExcursionModels
open SafeLearning.CompleteAppliedSupportConsequences
open SafeLearning.CompleteAppliedUniformDefinitions

theorem actual_every_nondegenerate_gaussian_has_strictly_positive_negative_probability
    (mean : ℝ) (variance : NNReal) (hv : 0<variance) :
    0<gaussianReal mean variance (Iio 0) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hvolume := gaussianReal_absolutelyContinuous' mean hv.ne' hz
  have hle := measure_mono (μ:=volume) (Ioo_subset_Iio_self : Ioo (-1:ℝ) 0 ⊆ Iio 0)
  rw [hvolume,Real.volume_Ioo] at hle
  norm_num at hle

theorem actual_excursion_preimage_splits_into_collapsed_and_positive_parts
    (event : Set ℝ) :
    (actualExcursion ⁻¹' event) ∩ Icc (-1) 1 =
      (if 0∈event then Icc (-1) 0 else ∅) ∪ (event ∩ Ioc 0 1) := by
  ext input
  by_cases hi : input≤0
  · have hm : actualExcursion input=0 := max_eq_right hi
    simp only [mem_inter_iff,mem_preimage,hm,mem_Icc,mem_union,mem_Ioc]
    split_ifs with he <;> simp only [mem_Icc,mem_empty_iff_false,false_or] <;> constructor
    · rintro ⟨_,hl,_⟩;exact Or.inl ⟨hl,hi⟩
    · rintro (⟨hl,_⟩|⟨_,hp,_⟩)
      · exact ⟨he,hl,by linarith⟩
      · linarith
    · rintro ⟨h,_,_⟩;exact (he h).elim
    · rintro ⟨_,hp,_⟩;linarith
  · have hp : 0 < input := lt_of_not_ge hi
    have hm : actualExcursion input=input := max_eq_left hp.le
    simp only [mem_inter_iff,mem_preimage,hm,mem_Icc,mem_union,mem_Ioc]
    split_ifs with he <;> simp only [mem_Icc,mem_empty_iff_false,false_or] <;> constructor
    · rintro ⟨hh,_,hu⟩;exact Or.inr ⟨hh,hp,hu⟩
    · rintro (⟨_,hn⟩|⟨hh,_,hu⟩)
      · linarith
      · exact ⟨hh,by linarith,hu⟩
    · rintro ⟨hh,_,hu⟩;exact ⟨hh,hp,hu⟩
    · rintro ⟨hh,_,hu⟩;exact ⟨hh,by linarith,hu⟩

theorem actual_excursion_law_is_half_atom_plus_half_positive_unit_density :
    actualExcursionLaw=(2:ENNReal)⁻¹ • Measure.dirac 0+
      (2:ENNReal)⁻¹ • volume.restrict (Ioc (0:ℝ) 1) := by
  ext event he
  rw [actualExcursionLaw,Measure.map_apply actual_excursion_is_continuous.measurable he,
    actualSignedLaw,actual_uniform_law_is_the_true_normalized_restriction (-1) 1 (by norm_num),
    Measure.smul_apply,Measure.restrict_apply
      (actual_excursion_is_continuous.measurable he),
    actual_excursion_preimage_splits_into_collapsed_and_positive_parts]
  norm_num only [sub_neg_eq_add,ENNReal.ofReal_ofNat]
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    Measure.restrict_apply he,Measure.dirac_apply' _ he]
  by_cases hz : 0∈event
  · rw [if_pos hz,measure_union]
    · rw [Real.volume_Icc,indicator_of_mem hz]
      norm_num [smul_eq_mul,mul_add]
    · rw [disjoint_iff_inter_eq_empty]
      ext input
      simp only [mem_inter_iff,mem_Icc,mem_Ioc,mem_empty_iff_false,iff_false]
      rintro ⟨⟨_,hn⟩,_,hp,_⟩
      linarith
    · exact he.inter measurableSet_Ioc
  · rw [if_neg hz,empty_union,indicator_of_notMem hz]
    simp

end SafeLearning.CompleteAppliedExcursionDecomposition
