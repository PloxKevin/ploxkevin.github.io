import SafeLearning.CompleteAppliedIndependencePitfalls
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace SafeLearning.CompleteAppliedEmpiricalLaw

def empiricalLaw {N : ℕ} {alpha : Type*} [MeasurableSpace alpha]
    (sample : Fin (N+1) → alpha) : Measure alpha :=
  (PMF.uniformOfFintype (Fin (N+1))).toMeasure.map sample

instance empiricalLaw_probability {N : ℕ} {alpha : Type*} [MeasurableSpace alpha]
    (sample : Fin (N+1) → alpha) : IsProbabilityMeasure (empiricalLaw sample) := by
  dsimp [empiricalLaw]
  exact Measure.isProbabilityMeasure_map (measurable_of_finite sample).aemeasurable

theorem actual_finite_empirical_law_is_a_probability_law
    {N : ℕ} {alpha : Type*} [MeasurableSpace alpha] (sample : Fin (N+1) → alpha) :
    empiricalLaw sample Set.univ=1 := by
  exact measure_univ

theorem actual_every_index_has_equal_empirical_weight
    (N : ℕ) (i : Fin (N+1)) :
    (PMF.uniformOfFintype (Fin (N+1))).toMeasure {i}=(N+1:ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin]
  simp only [Nat.cast_add,Nat.cast_one]

theorem actual_empirical_event_probability_counts_samples_with_repetitions
    {N : ℕ} {alpha : Type*} [MeasurableSpace alpha]
    (sample : Fin (N+1) → alpha) (A : Set alpha) (hA : MeasurableSet A) :
    empiricalLaw sample A=
      ((Finset.univ.filter (fun i => sample i∈A)).card:ℝ≥0∞)/(N+1:ℝ≥0∞) := by
  classical
  rw [empiricalLaw,Measure.map_apply (measurable_of_finite sample) hA]
  rw [PMF.uniformOfFintype,PMF.toMeasure_uniformOfFinset_apply]
  · simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    rfl
  · exact (measurable_of_finite sample) hA

theorem actual_empirical_expectation_is_the_arbitrary_finite_sample_mean
    {N : ℕ} (sample : Fin (N+1) → ℝ) :
    (∫ x,x ∂empiricalLaw sample)=(∑ i,sample i)/(N+1:ℝ) := by
  rw [empiricalLaw,integral_map (measurable_of_finite sample).aemeasurable
    measurable_id.aestronglyMeasurable,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Nat.cast_add,Nat.cast_one,smul_eq_mul]
  rw [←Finset.mul_sum,div_eq_inv_mul]

theorem actual_two_hundred_samples_each_have_mass_one_over_two_hundred
    (i : Fin 200) :
    (PMF.uniformOfFintype (Fin 200)).toMeasure {i}=1/200 := by
  convert actual_every_index_has_equal_empirical_weight 199 i using 1 <;> norm_num

theorem actual_two_hundred_sample_empirical_expectation_is_the_sample_mean
    (sample : Fin 200 → ℝ) :
    (∫ x,x ∂empiricalLaw (N:=199) sample)=(∑ i,sample i)/200 := by
  convert actual_empirical_expectation_is_the_arbitrary_finite_sample_mean (N:=199) sample using 1
  norm_num

theorem actual_sample_mean_of_measurable_observations_is_a_random_variable
    {Omega : Type*} [MeasurableSpace Omega] {N : ℕ}
    (sample : Fin (N+1) → Omega → ℝ) (h : ∀ i,Measurable (sample i)) :
    Measurable (fun o => (∑ i,sample i o)/(N+1:ℝ)) := by
  exact (Finset.measurable_sum _ (fun i _ => h i)).div_const _

end SafeLearning.CompleteAppliedEmpiricalLaw
