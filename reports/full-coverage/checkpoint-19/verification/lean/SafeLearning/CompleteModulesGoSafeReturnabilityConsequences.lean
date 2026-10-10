import SafeLearning.CompleteModulesGoSafeReturnability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeReturnabilityConsequences
open CompleteModulesGoSafeReturnability

def actualTargetReturnIterates (extraReturnAction : Bool) (target : Finset (Fin 5)) :
    ℕ→Finset (Fin 5)
  | 0 => target
  | n+1 => sourceReturnStep extraReturnAction (actualTargetReturnIterates extraReturnAction target n)

def actualTargetReturnClosure (extraReturnAction : Bool) (target : Finset (Fin 5)) : Set (Fin 5) :=
  {x | ∃ n,x∈actualTargetReturnIterates extraReturnAction target n}

def actualTargetErgodicUpdate (extraReturnAction : Bool) (old : Finset (Fin 5)) : Set (Fin 5) :=
  (sourceReachStep extraReturnAction old : Set (Fin 5))∩actualTargetReturnClosure extraReturnAction old

theorem actual_original_target_iterates_and_closure_are_the_original_passed_model
    (extra : Bool) :
    (∀ n,actualTargetReturnIterates extra sourceSeed n=sourceReturnIterates extra n) ∧
      actualTargetReturnClosure extra sourceSeed=sourceReturnClosure extra := by
  have hi : ∀ n,actualTargetReturnIterates extra sourceSeed n=sourceReturnIterates extra n := by
    intro n;induction n with
    | zero => rfl
    | succ n ih => rw [actualTargetReturnIterates,sourceReturnIterates,ih]
  exact ⟨hi,by ext x;simp only [actualTargetReturnClosure,sourceReturnClosure,Set.mem_setOf_eq,hi]⟩

theorem actual_the_enlarged_old_target_return_iterates_stabilize_after_one (n : ℕ) :
    actualTargetReturnIterates false {0,1,2} (n+1)={0,1,2,3} := by
  induction n with
  | zero => decide
  | succ n ih => rw [actualTargetReturnIterates,ih];decide

theorem actual_the_enlarged_old_target_return_closure_is_exactly_four_states :
    actualTargetReturnClosure false {0,1,2}=({0,1,2,3} : Set (Fin 5)) := by
  ext x;constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
      simp only [actualTargetReturnIterates,Finset.mem_insert,Finset.mem_singleton] at hn
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    | succ n =>
      rw [actual_the_enlarged_old_target_return_iterates_stabilize_after_one n] at hn
      simpa using hn
  · intro hx
    refine ⟨1,?_⟩
    rw [actual_the_enlarged_old_target_return_iterates_stabilize_after_one 0]
    simpa using hx

theorem actual_both_source_updates_use_their_actual_old_set_as_the_return_target :
    actualTargetErgodicUpdate false sourceSeed=({0,1,2} : Set (Fin 5)) ∧
      actualTargetErgodicUpdate false {0,1,2}=({0,1,2,3} : Set (Fin 5)) := by
  constructor
  · have h := (actual_original_target_iterates_and_closure_are_the_original_passed_model false).2
    rw [actualTargetErgodicUpdate,h]
    exact actual_initial_ergodic_update_adds_state_three_but_not_state_four_or_the_trap.1
  · rw [actualTargetErgodicUpdate,actual_the_enlarged_old_target_return_closure_is_exactly_four_states]
    have hr : sourceReachStep false {0,1,2}={0,1,2,3} := by decide
    rw [hr]
    ext x;fin_cases x <;> decide

theorem actual_the_trap_has_only_itself_as_a_successor (x : Fin 5) :
    sourceFiveEdge false 4 x=true ↔ x=4 := by
  fin_cases x <;> decide

theorem actual_any_graph_trajectory_that_visits_the_trap_stays_there_forever
    (path : ℕ→Fin 5) (hnext : ∀ n,sourceFiveEdge false (path n) (path (n+1))=true)
    (time : ℕ) (htrap : path time=4) : ∀ n,path (time+n)=4 := by
  intro n;induction n with
  | zero => simpa using htrap
  | succ n ih =>
    have he := hnext (time+n)
    rw [ih] at he
    exact (actual_the_trap_has_only_itself_as_a_successor _).mp he

theorem actual_return_step_is_monotone_in_its_target (extra : Bool)
    (small large : Finset (Fin 5)) (hsub : small⊆large) :
    sourceReturnStep extra small⊆sourceReturnStep extra large := by
  intro x hx
  simp only [sourceReturnStep,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
  rcases hx with hx|⟨y,hy,he⟩
  · exact Or.inl (hsub hx)
  · exact Or.inr ⟨y,hsub hy,he⟩

theorem actual_target_return_iterates_are_monotone_in_the_target (extra : Bool)
    (small large : Finset (Fin 5)) (hsub : small⊆large) :
    ∀ n,actualTargetReturnIterates extra small n⊆actualTargetReturnIterates extra large n := by
  intro n;induction n with
  | zero => exact hsub
  | succ n ih => exact actual_return_step_is_monotone_in_its_target extra _ _ ih

theorem actual_new_action_return_closure_is_complete_for_every_enlarged_old_seed
    (old : Finset (Fin 5)) (hseed : sourceSeed⊆old) :
    actualTargetReturnClosure true old=Set.univ := by
  ext x;simp only [Set.mem_univ,iff_true]
  refine ⟨3,?_⟩
  have hsub := actual_target_return_iterates_are_monotone_in_the_target true sourceSeed old hseed 3
  have hi := (actual_original_target_iterates_and_closure_are_the_original_passed_model true).1 3
  have hfull := actual_new_action_from_state_five_to_state_four_makes_the_third_return_iterate_complete.2.2
  rw [hi,hfull] at hsub
  exact hsub (Finset.mem_univ x)

theorem actual_with_the_new_action_every_state_is_explorable_exactly_when_one_step_reachable
    (old : Finset (Fin 5)) (hseed : sourceSeed⊆old) (x : Fin 5) :
    x∈actualTargetErgodicUpdate true old ↔ x∈sourceReachStep true old := by
  rw [actualTargetErgodicUpdate,actual_new_action_return_closure_is_complete_for_every_enlarged_old_seed old hseed]
  simp

end SafeLearning.CompleteModulesGoSafeReturnabilityConsequences
