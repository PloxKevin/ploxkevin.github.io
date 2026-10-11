import SafeLearning.CompleteAppliedCoverageUniformLaw
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCoverageContinuousTransform
open CompleteAppliedCoverageBeta CompleteAppliedCoverageUniformLaw
open CompleteAppliedCoverageOrderStatistic CompleteAppliedUniformDefinitions

theorem actual_continuous_cdf_attains_every_interior_probability
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (p : ℝ) (hp : p∈Ioo (0:ℝ) 1) : ∃x:ℝ,cdf law x=p := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (l₁:=atBot) (l₂:=atTop) (by simp) (by simp) hc.continuousOn
    (tendsto_cdf_atBot law) (tendsto_cdf_atTop law)
  obtain ⟨x,_,hx⟩:=h hp
  exact ⟨x,hx⟩

theorem actual_continuous_cdf_transform_closed_threshold_probability
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) :
    law.real {x|cdf law x≤p}=p := by
  have hupper : law.real {x|cdf law x≤p}≤p := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro q hq
    by_cases hq1 : q<1
    · obtain ⟨y,hy⟩:=actual_continuous_cdf_attains_every_interior_probability law hc q
        ⟨lt_of_le_of_lt hp.1 hq,hq1⟩
      have hs : {x|cdf law x≤p}⊆Iic y := by
        intro x hx
        by_contra hx'
        have hm := monotone_cdf law (le_of_not_ge hx')
        rw [hy] at hm
        exact (not_le_of_gt hq) (hm.trans hx)
      have h:=measureReal_mono (μ:=law) hs
      rw [←cdf_eq_real law y,hy] at h
      exact h
    · exact measureReal_le_one.trans (le_of_not_gt hq1)
  apply le_antisymm hupper
  by_cases hp0 : p=0
  · subst p;exact measureReal_nonneg
  · by_cases hp1 : p=1
    · subst p
      have he : {x|cdf law x≤(1:ℝ)}=univ:=by ext x;simp [cdf_le_one law x]
      rw [he,probReal_univ]
    · obtain ⟨y,hy⟩:=actual_continuous_cdf_attains_every_interior_probability law hc p
        ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
      have hs : Iic y⊆{x|cdf law x≤p}:=fun x hx=>by
        have h:=monotone_cdf law hx
        rwa [hy] at h
      have h:=measureReal_mono (μ:=law) hs
      rw [←cdf_eq_real law y,hy] at h
      exact h

theorem actual_continuous_cdf_probability_integral_transform_has_the_true_uniform_law
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law)) :
    HasLaw (cdf law) (actualUniformLaw 0 1) law := by
  haveI : IsProbabilityMeasure (actualUniformLaw 0 1):=
    actual_uniform_law_is_a_probability_measure 0 1 (by norm_num)
  haveI : NullSingletonClass (actualUniformLaw 0 1):=
    ⟨actual_unit_uniform_law_has_zero_singleton_mass⟩
  have heq : ∀p,p∈Icc (0:ℝ) 1→(law.map (cdf law)).real (Iic p)=
      (actualUniformLaw 0 1).real (Iic p) := by
    intro p hp
    rw [map_measureReal_apply hc.measurable measurableSet_Iic,
      ←measureReal_congr (Iio_ae_eq_Iic (μ:=actualUniformLaw 0 1) (a:=p)),
      actual_unit_uniform_strict_cdf p hp]
    exact actual_continuous_cdf_transform_closed_threshold_probability law hc p hp
  have h0 : (law.map (cdf law)).real (Iic (0:ℝ))=0 ∧
      (actualUniformLaw 0 1).real (Iic (0:ℝ))=0 := by
    have hu : (actualUniformLaw 0 1).real (Iic (0:ℝ))=0 := by
      rw [←measureReal_congr (Iio_ae_eq_Iic (μ:=actualUniformLaw 0 1) (a:=0)),
        actual_unit_uniform_strict_cdf 0 (by constructor <;>norm_num)]
    exact ⟨(heq 0 (by constructor <;>norm_num)).trans hu,hu⟩
  have h1 : (law.map (cdf law)).real (Iic (1:ℝ))=1 ∧
      (actualUniformLaw 0 1).real (Iic (1:ℝ))=1 := by
    have hu : (actualUniformLaw 0 1).real (Iic (1:ℝ))=1 := by
      rw [←measureReal_congr (Iio_ae_eq_Iic (μ:=actualUniformLaw 0 1) (a:=1)),
        actual_unit_uniform_strict_cdf 1 (by constructor <;>norm_num)]
    exact ⟨(heq 1 (by constructor <;>norm_num)).trans hu,hu⟩
  refine ⟨hc.measurable.aemeasurable,?_⟩
  apply Measure.ext_of_Iic
  intro p
  apply (measureReal_eq_measureReal_iff).mp
  by_cases hlo : 0≤p
  · by_cases hhi : p≤1
    · exact heq p ⟨hlo,hhi⟩
    · have hs : Iic (1:ℝ)⊆Iic p:=Iic_subset_Iic.mpr (le_of_not_ge hhi)
      have hl:=measureReal_mono (μ:=law.map (cdf law)) hs
      have hu:=measureReal_mono (μ:=actualUniformLaw 0 1) hs
      rw [h1.1] at hl;rw [h1.2] at hu
      exact (le_antisymm measureReal_le_one hl).trans (le_antisymm measureReal_le_one hu).symm
  · have hs : Iic p⊆Iic (0:ℝ):=Iic_subset_Iic.mpr (le_of_not_ge hlo)
    have hl:=measureReal_mono (μ:=law.map (cdf law)) hs
    have hu:=measureReal_mono (μ:=actualUniformLaw 0 1) hs
    rw [h0.1] at hl;rw [h0.2] at hu
    exact (le_antisymm hl measureReal_nonneg).trans (le_antisymm hu measureReal_nonneg).symm

theorem actual_monotone_cdf_commutes_with_the_second_largest (law : Measure ℝ)
    (scores : Fin 19→ℝ) :
    cdf law (secondLargest scores)=secondLargest (fun i=>cdf law (scores i)) := by
  classical
  unfold secondLargest
  rw [Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (cdf law)
    (fun x y=>(monotone_cdf law).map_sup x y)]
  congr 1
  funext pair
  exact (monotone_cdf law).map_min

theorem actual_iid_arbitrary_continuous_score_cdf_coverage_has_the_genuine_beta_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hind : iIndepFun scores P) (hlaw : ∀i,HasLaw (scores i) law P) :
    HasLaw (fun omega=>cdf law (secondLargest (fun i=>scores i omega))) coverageLaw P := by
  have hu:=actual_continuous_cdf_probability_integral_transform_has_the_true_uniform_law law hc
  have hi:=hind.comp (fun _=>cdf law) (fun _=>hc.measurable)
  have h:=actual_iid_uniform_second_largest_has_the_genuine_beta_law P
    (fun i omega=>cdf law (scores i omega)) (fun i=>hc.measurable.comp (hm i)) hi
    (fun i=>hu.comp (hlaw i))
  convert h using 1
  funext omega
  exact actual_monotone_cdf_commutes_with_the_second_largest law _

end SafeLearning.CompleteAppliedCoverageContinuousTransform
