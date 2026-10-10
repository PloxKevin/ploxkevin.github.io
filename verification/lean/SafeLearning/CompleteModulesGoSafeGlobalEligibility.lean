import SafeLearning.CompleteModulesGoSafeFailSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeGlobalEligibility
open CompleteModulesGoSafeDiscovery CompleteModulesGoSafeFailSet

def actualGlobalExplorationEligibility {A : Type*}
    (parameters certified excluded : Set A) : Set A := parameters\(certified∪excluded)

theorem actual_global_exploration_eligibility_is_exactly_the_literal_equation_eleven
    {A : Type*} (parameters certified excluded : Set A) (p : A) :
    p∈actualGlobalExplorationEligibility parameters certified excluded ↔
      p∈parameters ∧ p∉certified ∧ p∉excluded := by
  simp only [actualGlobalExplorationEligibility,Set.mem_diff,Set.mem_union,not_or]

theorem actual_permanent_exclusion_leaves_no_global_exploration_candidate_but_recheck_releases_the_optimum :
    actualGlobalExplorationEligibility (Set.univ : Set Bool) {false} {true}=∅ ∧
      actualGlobalExplorationEligibility (Set.univ : Set Bool) {false}
        (actualRecheckedExclusion {true} actualExpandedCoverage)={true} := by
  rw [actual_rechecking_the_newly_certified_interrupted_state_removes_its_exclusion]
  constructor <;> ext p <;> cases p <;> simp [actualGlobalExplorationEligibility]

theorem actual_new_global_candidate_has_the_genuine_attained_optimal_value_three :
    IsGreatest {value : ℝ | ∃ p,
      p∈actualGlobalExplorationEligibility (Set.univ : Set Bool) {false}
        (actualRecheckedExclusion {true} actualExpandedCoverage) ∧ sourceIslandValue p=value} 3 := by
  rw [actual_permanent_exclusion_leaves_no_global_exploration_candidate_but_recheck_releases_the_optimum.2]
  constructor
  · exact ⟨true,by simp,by norm_num [sourceIslandValue]⟩
  · rintro value ⟨p,hp,rfl⟩
    have he : p=true := hp
    rw [he];norm_num [sourceIslandValue]

theorem actual_permanent_exclusion_keeps_the_seed_incumbent_below_the_rechecked_attainable_optimum :
    IsGreatest {value : ℝ | ∃ p,
      p∈(({false}:Set Bool)∪actualGlobalExplorationEligibility Set.univ {false} {true}) ∧
        sourceIslandValue p=value} 1 ∧
      IsGreatest {value : ℝ | ∃ p,
        p∈(({false}:Set Bool)∪actualGlobalExplorationEligibility Set.univ {false}
          (actualRecheckedExclusion {true} actualExpandedCoverage)) ∧ sourceIslandValue p=value} 3 ∧
      (1:ℝ)<3 := by
  rw [actual_permanent_exclusion_leaves_no_global_exploration_candidate_but_recheck_releases_the_optimum.1,
    actual_permanent_exclusion_leaves_no_global_exploration_candidate_but_recheck_releases_the_optimum.2]
  simp only [Set.union_empty]
  constructor
  · constructor
    · exact ⟨false,by simp,by norm_num [sourceIslandValue]⟩
    · rintro value ⟨p,hp,rfl⟩
      have he : p=false := hp
      rw [he];norm_num [sourceIslandValue]
  constructor
  · constructor
    · exact ⟨true,by simp,by norm_num [sourceIslandValue]⟩
    · rintro value ⟨p,hp,rfl⟩
      cases p <;> norm_num [sourceIslandValue]
  · norm_num

end SafeLearning.CompleteModulesGoSafeGlobalEligibility
