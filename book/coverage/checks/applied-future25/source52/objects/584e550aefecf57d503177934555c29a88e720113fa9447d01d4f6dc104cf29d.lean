import SafeLearning.CompleteAppliedCoverageBetaCDF
import SafeLearning.CompleteAppliedCoverageOrderStatistic
import SafeLearning.CompleteAppliedUniformDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedCoverageUniformLaw
open CompleteAppliedCoverageBeta CompleteAppliedCoverageBetaCDF
open CompleteAppliedCoverageOrderStatistic CompleteAppliedUniformDefinitions

theorem actual_unit_uniform_strict_cdf (c : ℝ) (hc : c∈Icc (0:ℝ) 1) :
    (actualUniformLaw 0 1).real (Iio c)=c := by
  rw [measureReal_def,actual_uniform_probability_is_length_ratio 0 1 (by norm_num)
    (Iio c) measurableSet_Iio]
  have he : Iio c∩Icc (0:ℝ) 1=Ico (0:ℝ) c := by
    ext x
    simp only [mem_inter_iff,mem_Iio,mem_Icc,mem_Ico]
    constructor
    · intro h;exact ⟨h.2.1,h.1⟩
    · intro h;exact ⟨h.2,⟨h.1,le_trans h.2.le hc.2⟩⟩
  rw [he,Real.volume_Ico]
  norm_num
  exact hc.1

theorem actual_unit_uniform_law_has_zero_singleton_mass (c : ℝ) :
    actualUniformLaw 0 1 {c}=0 := by
  unfold actualUniformLaw CompleteAppliedDensityScaling.actualDensityLaw
  exact measure_singleton c

theorem actual_second_largest_is_an_actual_coordinate (scores : Fin 19→ℝ) :
    ∃i,secondLargest scores=scores i := by
  classical
  obtain ⟨pair,_,hp⟩:=Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun pair:DistinctPairs=>min (scores pair.1.1) (scores pair.1.2))
  change secondLargest scores=min (scores pair.1.1) (scores pair.1.2) at hp
  by_cases h : scores pair.1.1 ≤ scores pair.1.2
  · exact ⟨pair.1.1,hp.trans (min_eq_left h)⟩
  · exact ⟨pair.1.2,hp.trans (min_eq_right (le_of_not_ge h))⟩

theorem actual_atomless_coordinates_give_an_atomless_second_largest
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hn : ∀i c,P {omega|scores i omega=c}=0) :
    NullSingletonClass (P.map (fun omega=>secondLargest (fun i=>scores i omega))) := by
  constructor
  intro c
  rw [Measure.map_apply (actual_second_largest_of_measurable_coordinates_is_measurable scores hm)
    (measurableSet_singleton c)]
  apply measure_mono_null (t:=⋃i:Fin 19,{omega|scores i omega=c})
  · intro omega h
    obtain ⟨i,hi⟩:=actual_second_largest_is_an_actual_coordinate (fun i=>scores i omega)
    apply mem_iUnion.mpr
    exact ⟨i,hi.symm.trans h⟩
  · exact measure_iUnion_null (fun i=>hn i c)

theorem actual_iid_uniform_second_largest_has_the_genuine_beta_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hind : iIndepFun scores P) (hlaw : ∀i,HasLaw (scores i) (actualUniformLaw 0 1) P) :
    HasLaw (fun omega=>secondLargest (fun i=>scores i omega)) coverageLaw P := by
  let stat : Ω→ℝ:=fun omega=>secondLargest (fun i=>scores i omega)
  have hmeas : Measurable stat:=actual_second_largest_of_measurable_coordinates_is_measurable scores hm
  let Q : Measure ℝ:=P.map stat
  haveI : IsProbabilityMeasure Q:=by unfold Q;infer_instance
  haveI : NullSingletonClass Q:=actual_atomless_coordinates_give_an_atomless_second_largest P scores hm
    (fun i c=>by
      have h: P {omega|scores i omega=c}=(actualUniformLaw 0 1) {c}:=
        (hlaw i).measure_eq (measurableSet_singleton c)
      exact h.trans (actual_unit_uniform_law_has_zero_singleton_mass c))
  haveI : NullSingletonClass coverageLaw:=by
    unfold coverageLaw betaMeasure
    infer_instance
  have hcdf : ∀c,c∈Icc (0:ℝ) 1→Q.real (Iio c)=coverageLaw.real (Iio c) := by
    intro c hc
    have hp : ∀i,P.real {omega|scores i omega<c}=c:=fun i=>
      ((hlaw i).measureReal_eq measurableSet_Iio).trans (actual_unit_uniform_strict_cdf c hc)
    have h:=actual_iid_continuous_uniform_coordinate_count_gives_the_second_largest_cdf P scores hm hind c hp
    rw [actual_beta_strict_cdf_on_the_unit_interval c hc]
    change (P.map stat).real (Iio c)=_
    rw [map_measureReal_apply hmeas measurableSet_Iio]
    change P.real {omega|secondLargest (fun i=>scores i omega)<c}=_
    rw [h]
    ring
  have hzero : Q.real (Iio (0:ℝ))=0 ∧ coverageLaw.real (Iio (0:ℝ))=0 := by
    have hb:=actual_beta_strict_cdf_on_the_unit_interval 0 (by constructor <;>norm_num)
    norm_num at hb
    exact ⟨(hcdf 0 (by constructor <;>norm_num)).trans hb,hb⟩
  have hone : Q.real (Iio (1:ℝ))=1 ∧ coverageLaw.real (Iio (1:ℝ))=1 := by
    have hb:=actual_beta_strict_cdf_on_the_unit_interval 1 (by constructor <;>norm_num)
    norm_num at hb
    exact ⟨(hcdf 1 (by constructor <;>norm_num)).trans hb,hb⟩
  have hall : ∀c,Q.real (Iio c)=coverageLaw.real (Iio c) := by
    intro c
    by_cases hlo : 0≤c
    · by_cases hhi : c≤1
      · exact hcdf c ⟨hlo,hhi⟩
      · have hs : Iio (1:ℝ)⊆Iio c:=fun _ h=>lt_of_lt_of_le h (le_of_not_ge hhi)
        have hq := measureReal_mono (μ:=Q) hs
        have hb := measureReal_mono (μ:=coverageLaw) hs
        rw [hone.1] at hq
        rw [hone.2] at hb
        have hq1 : Q.real (Iio c)≤1:=measureReal_le_one
        have hb1 : coverageLaw.real (Iio c)≤1:=measureReal_le_one
        exact (le_antisymm hq1 hq).trans (le_antisymm hb1 hb).symm
    · have hs : Iio c⊆Iio (0:ℝ):=fun _ h=>lt_of_lt_of_le h (le_of_not_ge hlo)
      have hq := measureReal_mono (μ:=Q) hs
      have hb := measureReal_mono (μ:=coverageLaw) hs
      rw [hzero.1] at hq
      rw [hzero.2] at hb
      exact (le_antisymm hq measureReal_nonneg).trans (le_antisymm hb measureReal_nonneg).symm
  have he : Q=coverageLaw := by
    apply Measure.ext_of_Iic
    intro c
    apply (measureReal_eq_measureReal_iff).mp
    calc
      Q.real (Iic c)=Q.real (Iio c):=measureReal_congr Iio_ae_eq_Iic.symm
      _=coverageLaw.real (Iio c):=hall c
      _=coverageLaw.real (Iic c):=measureReal_congr Iio_ae_eq_Iic
  exact ⟨hmeas.aemeasurable,he⟩

end SafeLearning.CompleteAppliedCoverageUniformLaw
