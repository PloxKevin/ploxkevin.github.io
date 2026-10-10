import SafeLearning.CompleteModulesGoSafeReturnabilityConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeReturnabilityTrap
open CompleteModulesGoSafeReturnability CompleteModulesGoSafeReturnabilityConsequences

theorem actual_trap_exclusion_is_preserved_by_each_return_step
    (target : Finset (Fin 5)) (htrap : (4:Fin 5)∉target) :
    (4:Fin 5)∉sourceReturnStep false target := by
  intro h
  simp only [sourceReturnStep,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at h
  rcases h with h|⟨y,hy,he⟩
  · exact htrap h
  · have hy4 := (actual_the_trap_has_only_itself_as_a_successor y).mp he
    subst y
    exact htrap hy

theorem actual_trap_is_excluded_from_every_target_return_iterate
    (target : Finset (Fin 5)) (htrap : (4:Fin 5)∉target) :
    ∀ n,(4:Fin 5)∉actualTargetReturnIterates false target n := by
  intro n;induction n with
  | zero => exact htrap
  | succ n ih => exact actual_trap_exclusion_is_preserved_by_each_return_step _ ih

theorem actual_trap_is_excluded_from_the_whole_return_closure_and_ergodic_update
    (old : Finset (Fin 5)) (htrap : (4:Fin 5)∉old) :
    (4:Fin 5)∉actualTargetReturnClosure false old ∧
      (4:Fin 5)∉actualTargetErgodicUpdate false old := by
  have hc : (4:Fin 5)∉actualTargetReturnClosure false old := by
    rintro ⟨n,hn⟩
    exact actual_trap_is_excluded_from_every_target_return_iterate old htrap n hn
  exact ⟨hc,fun h=>hc h.2⟩

def actualFiniteErgodicUpdate (old : Finset (Fin 5)) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun x=>x∈actualTargetErgodicUpdate false old)

def actualIteratedErgodicSets : ℕ→Finset (Fin 5)
  | 0 => sourceSeed
  | n+1 => actualFiniteErgodicUpdate (actualIteratedErgodicSets n)

theorem actual_iterated_old_target_ergodic_updates_never_explore_the_trap :
    ∀ n,(4:Fin 5)∉actualIteratedErgodicSets n := by
  intro n;induction n with
  | zero => decide
  | succ n ih =>
    have h := (actual_trap_is_excluded_from_the_whole_return_closure_and_ergodic_update _ ih).2
    intro hx
    simp only [actualIteratedErgodicSets,actualFiniteErgodicUpdate,Finset.mem_filter,
      Finset.mem_univ,true_and] at hx
    exact h hx

end SafeLearning.CompleteModulesGoSafeReturnabilityTrap
