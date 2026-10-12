import SafeLearning.CompleteAppliedUniformDefinitions
import Mathlib.MeasureTheory.Measure.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
namespace SafeLearning.CompleteAppliedAlmostSureBridges
open SafeLearning.CompleteAppliedUniformDefinitions SafeLearning.CompleteAppliedDensityScaling

variable {Ω : Type*} [MeasurableSpace Ω]

def actualPositiveThreshold (quantity : Ω → ℝ) (n : ℕ) : Set Ω :=
  {point | 1/((n:ℝ)+1) ≤ quantity point}

theorem actual_threshold_indicator_lower_bound (quantity : Ω → ℝ)
    (hnon : ∀ point,0 ≤ quantity point) (n : ℕ) :
    ∀ point, (actualPositiveThreshold quantity n).indicator
      (fun _ => 1/((n:ℝ)+1)) point ≤ quantity point := by
  intro point
  by_cases hp : point ∈ actualPositiveThreshold quantity n
  · simpa only [indicator_of_mem hp] using (show 1/((n:ℝ)+1) ≤ quantity point from hp)
  · simpa only [indicator_of_notMem hp] using hnon point

theorem actual_zero_nonnegative_expectation_makes_every_positive_threshold_null
    (P : Measure Ω) [IsProbabilityMeasure P] (quantity : Ω → ℝ)
    (hmeas : Measurable quantity) (hint : Integrable quantity P)
    (hnon : ∀ point,0 ≤ quantity point) (hzero : (∫ point,quantity point ∂P)=0) (n : ℕ) :
    P (actualPositiveThreshold quantity n)=0 := by
  have hm : MeasurableSet (actualPositiveThreshold quantity n) :=
    measurableSet_le measurable_const hmeas
  have hi : Integrable ((actualPositiveThreshold quantity n).indicator
      (fun _ => 1/((n:ℝ)+1))) P := integrable_const _ |>.indicator hm
  have hb := integral_mono hi hint (actual_threshold_indicator_lower_bound quantity hnon n)
  rw [integral_indicator hm,integral_const,measureReal_restrict_apply MeasurableSet.univ,
    univ_inter,smul_eq_mul,hzero] at hb
  have hp : 0 < 1/((n:ℝ)+1) := by positivity
  have hz : P.real (actualPositiveThreshold quantity n)=0 := by
    have hn := measureReal_nonneg (μ:=P) (s:=actualPositiveThreshold quantity n)
    nlinarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top P _)

theorem actual_positive_event_is_the_countable_union_of_positive_threshold_events
    (quantity : Ω → ℝ) :
    {point | 0 < quantity point}=⋃ n : ℕ,actualPositiveThreshold quantity n := by
  ext point
  constructor
  · intro hp
    change 0 < quantity point at hp
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
    exact mem_iUnion.mpr ⟨n,by exact hn.le⟩
  · intro hp
    obtain ⟨n,hn⟩ := mem_iUnion.mp hp
    exact lt_of_lt_of_le (by positivity : 0 < 1/((n:ℝ)+1)) hn

theorem actual_nonnegative_zero_expectation_implies_almost_sure_zero_via_the_source_countable_union
    (P : Measure Ω) [IsProbabilityMeasure P] (quantity : Ω → ℝ)
    (hmeas : Measurable quantity) (hint : Integrable quantity P)
    (hnon : ∀ point,0 ≤ quantity point) (hzero : (∫ point,quantity point ∂P)=0) :
    quantity =ᵐ[P] 0 := by
  have hz : P {point | 0 < quantity point}=0 := by
    rw [actual_positive_event_is_the_countable_union_of_positive_threshold_events,measure_iUnion_null_iff]
    exact actual_zero_nonnegative_expectation_makes_every_positive_threshold_null P quantity hmeas hint hnon hzero
  have ha : ∀ᵐ point ∂P, ¬0 < quantity point := by simpa [ae_iff] using hz
  filter_upwards [ha] with point hp
  exact le_antisymm (le_of_not_gt hp) (hnon point)

theorem actual_continuity_upgrades_an_almost_sure_upper_bound_to_every_support_point
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (P : Measure X)
    (quantity : X → ℝ) (hcontinuous : Continuous quantity) (upper : ℝ)
    (hae : ∀ᵐ point ∂P,quantity point ≤ upper) :
    ∀ point ∈ P.support,quantity point ≤ upper := by
  exact P.support_subset_of_isClosed (isClosed_le hcontinuous continuous_const) hae

theorem actual_standard_gaussian_has_full_measure_support :
    (gaussianReal 0 1).support=univ := by
  have he : (volume : Measure ℝ).support=univ := Measure.support_eq_univ
  have hsub := (gaussianReal_absolutelyContinuous' (0:ℝ) (by norm_num : (1:NNReal)≠0)).support_mono
  exact eq_univ_of_univ_subset (he ▸ hsub)

def actualSpike (height point : ℝ) (input : ℝ) : ℝ := if input=point then height else 0

theorem actual_uniform_singleton_spike_is_nonnegative_ae_zero_but_nonzero_at_its_point
    (left right point height : ℝ) (hinterval : left < right) (hheight : 0 < height) :
    IsProbabilityMeasure (actualUniformLaw left right) ∧
      (∀ input,0 ≤ actualSpike height point input) ∧
      actualSpike height point =ᵐ[actualUniformLaw left right] 0 ∧
      Integrable (actualSpike height point) (actualUniformLaw left right) ∧
      (∫ input,actualSpike height point input ∂actualUniformLaw left right)=0 ∧
      actualSpike height point point=height ∧ actualSpike height point point≠0 := by
  have hzero : actualUniformLaw left right {point}=0 := by
    exact withDensity_absolutelyContinuous volume _ (measure_singleton point)
  have hae : actualSpike height point =ᵐ[actualUniformLaw left right] 0 := by
    have hpoint : ∀ᵐ input ∂actualUniformLaw left right,input≠point := by
      rw [ae_iff]
      convert hzero using 2
      ext input
      simp
    filter_upwards [hpoint] with input hp
    simp [actualSpike,hp]
  have hi : Integrable (actualSpike height point) (actualUniformLaw left right) :=
    (integrable_zero ℝ ℝ _).congr hae.symm
  refine ⟨actual_uniform_law_is_a_probability_measure left right hinterval,?_,hae,hi,?_,?_,?_⟩
  · intro input
    by_cases hp : input=point <;> simp [actualSpike,hp,hheight.le]
  · rw [integral_congr_ae hae]
    simp
  · simp [actualSpike]
  · simpa only [actualSpike,ite_true] using hheight.ne'

end SafeLearning.CompleteAppliedAlmostSureBridges
