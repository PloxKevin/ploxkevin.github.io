import SafeLearning.CompleteAppliedAlmostSureBridges
import Mathlib.MeasureTheory.Function.EssSup

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
namespace SafeLearning.CompleteAppliedMeasureSupport
open SafeLearning.CompleteAppliedAlmostSureBridges SafeLearning.CompleteAppliedUniformDefinitions

theorem actual_metric_measure_support_is_exactly_positive_measure_of_every_open_ball
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (P : Measure X) (point : X) :
    point ∈ P.support ↔ ∀ radius>0,0 < P (Metric.ball point radius) :=
  Metric.nhds_basis_ball.mem_measureSupport

theorem actual_real_measure_support_is_closed_has_full_mass_and_is_the_least_closed_full_mass_set
    (P : Measure ℝ) :
    IsClosed P.support ∧ P P.supportᶜ=0 ∧
      (∀ closedSet : Set ℝ,IsClosed closedSet → P closedSetᶜ=0 → P.support ⊆ closedSet) := by
  refine ⟨P.isClosed_support,P.measure_compl_support,?_⟩
  intro closedSet hclosed hmass
  exact P.support_subset_of_isClosed hclosed hmass

theorem actual_uniform_interval_support_is_the_exact_closed_interval
    (left right : ℝ) (hlt : left < right) :
    (actualUniformLaw left right).support=Icc left right := by
  let c : ENNReal := (ENNReal.ofReal (right-left))⁻¹
  have hc : c ≠ 0 := by simp only [c,ne_eq,ENNReal.inv_eq_zero,ENNReal.ofReal_ne_top,not_false_eq_true]
  have he := actual_uniform_law_is_the_true_normalized_restriction left right hlt
  have hac : volume.restrict (Icc left right) ≪ actualUniformLaw left right := by
    rw [he]
    exact Measure.absolutelyContinuous_smul hc
  have hi : Ioo left right ⊆ (actualUniformLaw left right).support := by
    intro point hp
    apply hac.support_mono
    apply (volume : Measure ℝ).interior_inter_support
    refine ⟨?_,?_⟩
    · simpa only [interior_Icc] using hp
    · rw [Measure.support_eq_univ]
      exact mem_univ _
  have hlo : Icc left right ⊆ (actualUniformLaw left right).support := by
    rw [← closure_Ioo hlt.ne]
    exact closure_minimal hi (actualUniformLaw left right).isClosed_support
  have hz : actualUniformLaw left right (Icc left right)ᶜ=0 := by
    rw [he,Measure.smul_apply,Measure.restrict_apply isClosed_Icc.measurableSet.compl]
    simp
  have hup := (actualUniformLaw left right).support_subset_of_isClosed isClosed_Icc hz
  exact subset_antisymm hup hlo

theorem actual_dirac_support_is_the_singleton
    (point : ℝ) : (Measure.dirac point).support={point} := by
  have hup : (Measure.dirac point).support ⊆ ({point}:Set ℝ) :=
    (Measure.dirac point).support_subset_of_isClosed isClosed_singleton (by simp)
  have hlo : ({point}:Set ℝ) ⊆ (Measure.dirac point).support := by
    intro input hp
    have hi : input=point := hp
    rw [hi,actual_metric_measure_support_is_exactly_positive_measure_of_every_open_ball]
    intro radius hr
    simp only [Measure.dirac_apply' _ measurableSet_ball,indicator_of_mem (Metric.mem_ball_self hr)]
    norm_num
  exact subset_antisymm hup hlo

theorem actual_zero_variance_gaussian_support_is_the_singleton_zero :
    (gaussianReal 0 0).support={0} := by
  rw [gaussianReal_zero_var]
  exact actual_dirac_support_is_the_singleton 0

theorem actual_positive_variance_gaussian_has_full_support (mean : ℝ) (variance : NNReal)
    (hv : 0 < variance) : (gaussianReal mean variance).support=univ := by
  have he : (volume : Measure ℝ).support=univ := Measure.support_eq_univ
  have hsub := (gaussianReal_absolutelyContinuous' mean hv.ne').support_mono
  exact eq_univ_of_univ_subset (he ▸ hsub)

/-- Extended-real essential supremum keeps the genuinely unbounded case as infinity. -/
theorem actual_extended_essential_supremum_is_the_infimum_of_probability_one_upper_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (quantity : Ω → EReal) (hmeas : Measurable quantity) :
    essSup quantity P=sInf {upper : EReal | P {point | quantity point ≤ upper}=1} := by
  rw [essSup_eq_sInf]
  congr 1
  ext upper
  have he : {point | upper < quantity point}={point | quantity point ≤ upper}ᶜ := by
    ext point
    simp
  simp only [mem_ofPred_eq,he]
  exact prob_compl_eq_zero_iff (measurableSet_le hmeas measurable_const)

theorem actual_singleton_spike_has_worst_case_ten_but_true_essential_supremum_zero :
    IsGreatest (range (actualSpike 10 (1/2))) 10 ∧
      essSup (actualSpike 10 (1/2)) (actualUniformLaw 0 1)=0 ∧
      (actualUniformLaw 0 1) {input | actualSpike 10 (1/2) input=0}=1 := by
  have h := actual_uniform_singleton_spike_is_nonnegative_ae_zero_but_nonzero_at_its_point
    (0:ℝ) 1 (1/2) 10 (by norm_num) (by norm_num)
  let : IsProbabilityMeasure (actualUniformLaw 0 1) := h.1
  have hn : actualUniformLaw 0 1≠0 := by
    intro hz
    have hu := measure_univ (μ:=actualUniformLaw 0 1)
    simp [hz] at hu
  refine ⟨⟨⟨1/2,by simp [actualSpike]⟩,?_⟩,?_,?_⟩
  · rintro value ⟨input,rfl⟩
    dsimp [actualSpike]
    split_ifs <;> norm_num
  · rw [essSup_congr_ae h.2.2.1]
    exact essSup_const 0 hn
  · apply (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (by
      change Measurable (fun input : ℝ => if input=(1/2:ℝ) then (10:ℝ) else 0)
      exact measurable_const.ite (measurableSet_singleton (1/2)) measurable_const) measurable_const)).mp
    change ∀ᵐ input ∂actualUniformLaw 0 1, actualSpike 10 (1/2) input=0
    exact h.2.2.1

end SafeLearning.CompleteAppliedMeasureSupport
