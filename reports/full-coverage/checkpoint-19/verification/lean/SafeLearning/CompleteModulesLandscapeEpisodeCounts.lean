import SafeLearning.CompleteAppliedBandit
import Mathlib.Probability.HasLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SafeLearning.CompleteModulesLandscapeEpisodeCounts
open CompleteAppliedProbability CompleteAppliedBandit

def episodeLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(9/10:ℝ≥0),1/10] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])
def episodeCount : Fin 2 → ℝ := ![0,5]
def unsafeStepCost (episode : Fin 2) (_time : Fin 5) : ℝ := if episode=1 then 1 else 0

theorem actual_episode_count_is_the_sum_of_five_indicator_costs (episode : Fin 2) :
    episodeCount episode=∑ time : Fin 5,unsafeStepCost episode time := by
  fin_cases episode <;> norm_num [episodeCount,unsafeStepCost]

theorem actual_episode_count_atom_probabilities :
    episodeLaw.toMeasure.real {i | episodeCount i=0}=9/10 ∧
    episodeLaw.toMeasure.real {i | episodeCount i=5}=1/10 := by
  have h0 : {i | episodeCount i=0}=({0}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [episodeCount]
  have h5 : {i | episodeCount i=5}=({1}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [episodeCount]
  rw [h0,h5]
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (0:Fin 2)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
  norm_num [episodeLaw]

theorem actual_source_expected_unsafe_steps :
    (∫ episode,episodeCount episode ∂episodeLaw.toMeasure)=1/2 := by
  rw [←finite_expectation_is_actual_integral]
  norm_num [finiteExpectation,episodeLaw,episodeCount,Fin.sum_univ_succ]

theorem actual_source_any_violation_event_and_probability :
    {i | 1 ≤ episodeCount i}=({1}:Set (Fin 2)) ∧
    episodeLaw.toMeasure.real {i | 1 ≤ episodeCount i}=1/10 := by
  have h : {i | 1 ≤ episodeCount i}=({1}:Set (Fin 2)) := by
    ext i;fin_cases i <;> norm_num [episodeCount]
  refine ⟨h,?_⟩
  rw [h]
  unfold Measure.real
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1:Fin 2))]
  norm_num [episodeLaw]

theorem actual_source_expected_cost_passes_and_episode_chance_fails :
    (∫ episode,episodeCount episode ∂episodeLaw.toMeasure) ≤ (0.6:ℝ) ∧
    ¬episodeLaw.toMeasure.real {i | 1 ≤ episodeCount i} ≤ (0.05:ℝ) := by
  rw [actual_source_expected_unsafe_steps,actual_source_any_violation_event_and_probability.2]
  norm_num

/-- The two-atom assumption is a law, so the conclusion holds on any source
probability space with that actual count distribution. -/
theorem actual_same_count_law_has_the_same_mean_and_event_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (count : Ω → ℝ)
    (h : HasLaw count (Measure.map episodeCount episodeLaw.toMeasure) μ) :
    (∫ ω,count ω ∂μ)=1/2 ∧ μ.real {ω | 1 ≤ count ω}=1/10 := by
  have hsource : HasLaw episodeCount (Measure.map episodeCount episodeLaw.toMeasure) episodeLaw.toMeasure :=
    hasLaw_map (measurable_of_finite episodeCount).aemeasurable
  constructor
  · rw [h.integral_eq,←hsource.integral_eq]
    exact actual_source_expected_unsafe_steps
  · rw [h.measureReal_eq measurableSet_Ici,←hsource.measureReal_eq measurableSet_Ici]
    exact actual_source_any_violation_event_and_probability.2

/-- Changing physical magnitudes does not change these indicator counts. -/
theorem actual_identical_indicator_counts_can_have_distinct_magnitude_costs :
    (∫ i,∑ t : Fin 5,unsafeStepCost i t ∂episodeLaw.toMeasure)=1/2 ∧
    (∫ i,∑ t : Fin 5,10*unsafeStepCost i t ∂episodeLaw.toMeasure)=5 := by
  constructor
  · simpa only [←actual_episode_count_is_the_sum_of_five_indicator_costs] using actual_source_expected_unsafe_steps
  · rw [←finite_expectation_is_actual_integral]
    norm_num [finiteExpectation,episodeLaw,unsafeStepCost,Fin.sum_univ_succ]

end SafeLearning.CompleteModulesLandscapeEpisodeCounts
