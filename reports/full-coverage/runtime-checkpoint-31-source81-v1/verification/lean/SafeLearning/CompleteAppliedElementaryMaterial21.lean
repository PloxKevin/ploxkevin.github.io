import SafeLearning.CompleteAppliedProbability

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedElementaryMaterial21
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open CompleteAppliedProbability

theorem actual_event_and_complement_are_a_partition {Outcome : Type*}
    (event : Set Outcome) :
    event ∪ eventᶜ = Set.univ ∧ Disjoint event eventᶜ := by
  exact ⟨Set.union_compl_self event, disjoint_compl_right⟩

theorem actual_fair_die_conditioned_on_above_three_has_exactly_three_equal_atoms
    (outcome : Fin 6) :
    (outcome ∈ dieAboveThree ↔ outcome.val + 1 = 4 ∨ outcome.val + 1 = 5 ∨
      outcome.val + 1 = 6) ∧
    conditionalProbability fairDie {outcome} dieAboveThree =
      if 3 < outcome.val + 1 then 1/3 else 0 := by
  fin_cases outcome <;>
    norm_num [conditionalProbability,eventProbability,fairDie,dieAboveThree,
      PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

end SafeLearning.CompleteAppliedElementaryMaterial21
