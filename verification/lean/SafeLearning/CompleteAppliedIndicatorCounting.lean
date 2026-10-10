import SafeLearning.CompleteModulesLandscapeFiniteCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set
namespace SafeLearning.CompleteAppliedIndicatorCounting
open SafeLearning.CompleteModulesLandscapeFiniteCounts

theorem actual_fifty_dependent_step_violations_have_expected_count_one_fifth_and_event_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (events : Fin 50 → Set Ω) (hmeas : ∀ time,MeasurableSet (events time))
    (hmarginal : ∀ time,P.real (events time)=1/250) :
    (∫ point,unsafeCount (T:=49) events point ∂P)=1/5 ∧
      P.real (everUnsafe events)≤1/5 := by
  have he := actual_expected_indicator_count_is_sum_of_marginal_probabilities P events hmeas
  simp only [hmarginal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  norm_num at he
  have hp := (actual_failure_probability_and_expected_count_control_each_other_only_up_to_horizon P events hmeas).1
  rw [he] at hp
  exact ⟨he,hp⟩

def actualSignedBooleanMonitor (event : Set ℝ) (input : ℝ) : ℝ :=
  event.indicator (fun _ => (1:ℝ)) input-1/2

theorem actual_boolean_indicator_minus_one_half_is_a_signed_monitor
    {Ω : Type*} (event : Set Ω) (point : Ω) :
    event.indicator (fun _ => (1:ℝ)) point-1/2 ∈ ({-1/2,1/2}:Set ℝ) ∧
      (0<event.indicator (fun _ => (1:ℝ)) point-1/2 ↔ point∈event) := by
  classical
  by_cases hp : point∈event <;> simp [Set.indicator,hp] <;> norm_num

end SafeLearning.CompleteAppliedIndicatorCounting
