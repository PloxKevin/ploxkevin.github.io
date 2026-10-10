import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesGoSafeReturnability

/-- Literal five-state graph, with the optional new action from the trap to state4. -/
def sourceFiveEdge (extraReturnAction : Bool) (x y : Fin 5) : Bool :=
  ((x.val==0) && ((y.val==0)||(y.val==1))) ||
  ((x.val==1) && ((y.val==0)||(y.val==2))) ||
  ((x.val==2) && ((y.val==1)||(y.val==3))) ||
  ((x.val==3) && ((y.val==2)||(y.val==4))) ||
  ((x.val==4) && ((y.val==4)||(extraReturnAction && (y.val==3))))

def sourceSeed : Finset (Fin 5) := {0,1}

def sourceReachStep (extraReturnAction : Bool) (seed : Finset (Fin 5)) : Finset (Fin 5) :=
  seed∪Finset.univ.filter (fun y=>∃ x∈seed,sourceFiveEdge extraReturnAction x y=true)

def sourceReturnStep (extraReturnAction : Bool) (target : Finset (Fin 5)) : Finset (Fin 5) :=
  target∪Finset.univ.filter (fun x=>∃ y∈target,sourceFiveEdge extraReturnAction x y=true)

def sourceReturnIterates (extraReturnAction : Bool) : ℕ→Finset (Fin 5)
  | 0 => sourceSeed
  | n+1 => sourceReturnStep extraReturnAction (sourceReturnIterates extraReturnAction n)

def sourceReturnClosure (extraReturnAction : Bool) : Set (Fin 5) :=
  {x | ∃ n,x∈sourceReturnIterates extraReturnAction n}

def sourceErgodicUpdate (extraReturnAction : Bool) (old : Finset (Fin 5)) : Set (Fin 5) :=
  (sourceReachStep extraReturnAction old : Set (Fin 5))∩sourceReturnClosure extraReturnAction

theorem actual_source_reachability_and_each_three_returnability_iterates :
    sourceReachStep false sourceSeed={0,1,2} ∧
      sourceReturnIterates false 1={0,1,2} ∧
      sourceReturnIterates false 2={0,1,2,3} ∧
      sourceReturnIterates false 3={0,1,2,3} := by decide

theorem actual_all_return_iterates_after_the_second_stabilize (n : ℕ) :
    sourceReturnIterates false (n+2)={0,1,2,3} := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,sourceReturnIterates,ih]
    decide

theorem actual_full_source_returnability_closure_is_exactly_four_states :
    sourceReturnClosure false=({0,1,2,3} : Set (Fin 5)) := by
  ext x;constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
      simp only [sourceReturnIterates,sourceSeed,Finset.mem_insert,Finset.mem_singleton] at hn
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    | succ n =>
      cases n with
      | zero =>
        have hh : sourceReturnIterates false 1={0,1,2} := by decide
        rw [hh] at hn
        simp only [Finset.mem_insert,Finset.mem_singleton] at hn
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
        tauto
      | succ n =>
        rw [show n+1+1=n+2 by omega,actual_all_return_iterates_after_the_second_stabilize n] at hn
        simpa using hn
  · intro hx
    refine ⟨2,?_⟩
    rw [show sourceReturnIterates false 2={0,1,2,3} by decide]
    simpa using hx

theorem actual_initial_ergodic_update_adds_state_three_but_not_state_four_or_the_trap :
    sourceErgodicUpdate false sourceSeed=({0,1,2} : Set (Fin 5)) ∧
      (3:Fin 5)∈sourceReturnClosure false ∧
      (3:Fin 5)∉sourceErgodicUpdate false sourceSeed ∧
      (4:Fin 5)∉sourceReturnClosure false := by
  rw [sourceErgodicUpdate,actual_full_source_returnability_closure_is_exactly_four_states,
    actual_source_reachability_and_each_three_returnability_iterates.1]
  constructor
  · ext x;fin_cases x <;> decide
  norm_num

theorem actual_next_ergodic_update_adds_state_four_without_ever_adding_the_trap :
    sourceErgodicUpdate false {0,1,2}=({0,1,2,3} : Set (Fin 5)) := by
  rw [sourceErgodicUpdate,actual_full_source_returnability_closure_is_exactly_four_states]
  have hr : sourceReachStep false {0,1,2}={0,1,2,3} := by decide
  rw [hr]
  ext x;fin_cases x <;> decide

theorem actual_new_action_from_state_five_to_state_four_makes_the_third_return_iterate_complete :
    sourceReturnIterates true 1={0,1,2} ∧
      sourceReturnIterates true 2={0,1,2,3} ∧
      sourceReturnIterates true 3=Finset.univ := by decide

theorem actual_every_return_iterate_after_the_third_with_the_new_action_is_complete (n : ℕ) :
    sourceReturnIterates true (n+3)=Finset.univ := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n+1+3=(n+3)+1 by omega,sourceReturnIterates,ih]
    decide

theorem actual_new_action_gives_the_full_five_state_closure :
    sourceReturnClosure true=Set.univ := by
  ext x;simp only [Set.mem_univ,iff_true]
  refine ⟨3,?_⟩
  rw [actual_new_action_from_state_five_to_state_four_makes_the_third_return_iterate_complete.2.2]
  exact Finset.mem_univ x

theorem actual_with_the_new_action_state_five_becomes_explorable_when_one_step_reachable :
    sourceErgodicUpdate true {0,1,2,3}=Set.univ := by
  rw [sourceErgodicUpdate,actual_new_action_gives_the_full_five_state_closure]
  have hr : sourceReachStep true {0,1,2,3}=Finset.univ := by decide
  simp [hr]

end SafeLearning.CompleteModulesGoSafeReturnability
