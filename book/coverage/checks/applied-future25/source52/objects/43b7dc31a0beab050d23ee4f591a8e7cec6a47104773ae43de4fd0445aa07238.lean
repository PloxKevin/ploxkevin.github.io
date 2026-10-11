import SafeLearning.CompleteAppliedMeasureSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
namespace SafeLearning.CompleteAppliedSupportConsequences
open SafeLearning.CompleteAppliedMeasureSupport SafeLearning.CompleteAppliedAlmostSureBridges
open SafeLearning.CompleteAppliedUniformDefinitions SafeLearning.CompleteAppliedDensityScaling

theorem actual_support_in_arbitrary_second_countable_metric_space_is_closed_full_mass_and_least
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    (P : Measure X) :
    IsClosed P.support ∧ P P.supportᶜ=0 ∧
      (∀ closedSet : Set X,IsClosed closedSet → P closedSetᶜ=0 → P.support ⊆ closedSet) := by
  refine ⟨P.isClosed_support,P.measure_compl_support,?_⟩
  intro closedSet hc hm
  exact P.support_subset_of_isClosed hc hm

theorem actual_every_finite_euclidean_measure_support_has_the_source_ball_and_least_closed_characterizations
    (dimension : ℕ) (P : Measure (EuclideanSpace ℝ (Fin dimension))) :
    (∀ point, point ∈ P.support ↔ ∀ radius>0,0<P (Metric.ball point radius)) ∧
      IsClosed P.support ∧ P P.supportᶜ=0 ∧
      (∀ closedSet,IsClosed closedSet → P closedSetᶜ=0 → P.support ⊆ closedSet) := by
  refine ⟨actual_metric_measure_support_is_exactly_positive_measure_of_every_open_ball P,?_⟩
  exact actual_support_in_arbitrary_second_countable_metric_space_is_closed_full_mass_and_least P

theorem actual_uniform_random_value_avoids_a_specified_possible_point_almost_surely
    (point : ℝ) (hp : point ∈ Icc (0:ℝ) 1) :
    (actualUniformLaw 0 1) {input | input≠point}=1 ∧ point ∈ (actualUniformLaw 0 1).support := by
  let : IsProbabilityMeasure (actualUniformLaw 0 1) := actual_uniform_law_is_a_probability_measure 0 1 (by norm_num)
  have hz : actualUniformLaw 0 1 {point}=0 :=
    withDensity_absolutelyContinuous volume _ (measure_singleton point)
  constructor
  · have he : {input : ℝ | input≠point}=({point}:Set ℝ)ᶜ := by ext input;simp
    rw [he]
    exact (prob_compl_eq_one_iff (measurableSet_singleton point)).mpr hz
  · rw [actual_uniform_interval_support_is_the_exact_closed_interval 0 1 (by norm_num)]
    exact hp

def actualExcursion (input : ℝ) : ℝ := max input 0

theorem actual_uniform_excursion_has_the_true_essential_supremum_one :
    essSup actualExcursion (actualUniformLaw (-1) 1)=1 ∧
      IsLeast {upper : ℝ | actualUniformLaw (-1) 1 {input | actualExcursion input≤upper}=1} 1 := by
  let P := actualUniformLaw (-1) 1
  let : IsProbabilityMeasure P := actual_uniform_law_is_a_probability_measure (-1) 1 (by norm_num)
  have hcont : Continuous actualExcursion := continuous_id.max continuous_const
  have hupper : ∀ᵐ input ∂P,actualExcursion input≤1 := by
    filter_upwards [P.support_mem_ae] with input hi
    rw [actual_uniform_interval_support_is_the_exact_closed_interval (-1) 1 (by norm_num)] at hi
    exact max_le hi.2 (by norm_num)
  have hm (upper : ℝ) : MeasurableSet {input | actualExcursion input≤upper} :=
    measurableSet_le hcont.measurable measurable_const
  have hleast : IsLeast {upper : ℝ | P {input | actualExcursion input≤upper}=1} 1 := by
    constructor
    · exact (mem_ae_iff_prob_eq_one (hm 1)).mp hupper
    · intro upper hu
      have ha : ∀ᵐ input ∂P,actualExcursion input≤upper :=
        (mem_ae_iff_prob_eq_one (hm upper)).mpr hu
      have hp : (1:ℝ) ∈ P.support := by
        rw [actual_uniform_interval_support_is_the_exact_closed_interval (-1) 1 (by norm_num)]
        norm_num
      have hh := actual_continuity_upgrades_an_almost_sure_upper_bound_to_every_support_point
        P actualExcursion hcont upper ha 1 hp
      simpa only [actualExcursion,max_eq_left (by norm_num : (0:ℝ)≤1)] using hh
  refine ⟨?_,hleast⟩
  rw [essSup_eq_sInf]
  have he : {upper : ℝ | P {input | upper<actualExcursion input}=0}=
      {upper : ℝ | P {input | actualExcursion input≤upper}=1} := by
    ext upper
    have hc : {input | upper<actualExcursion input}={input | actualExcursion input≤upper}ᶜ := by
      ext input;simp
    simp only [mem_ofPred_eq,hc]
    exact prob_compl_eq_zero_iff (hm upper)
  rw [he]
  exact hleast.csInf_eq

end SafeLearning.CompleteAppliedSupportConsequences
