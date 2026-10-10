import SafeLearning.CompleteFoundationsGraphViability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsBreadthFirstSearch
open CompleteFoundationsGraphViability CompleteFoundationsFiniteSetIteration
variable {State : Type*}

def breadthFirst (edge : State → State → Prop) (seed : Set State) :
    ℕ → Set State × Set State
  | 0 => (seed,seed)
  | n+1 =>
    let old := breadthFirst edge seed n
    let fresh := graphPost edge old.2 \ old.1
    (old.1∪fresh,fresh)

def visited (edge : State → State → Prop) (seed : Set State) (n : ℕ) :=
  (breadthFirst edge seed n).1
def frontier (edge : State → State → Prop) (seed : Set State) (n : ℕ) :=
  (breadthFirst edge seed n).2

def exactLengthPath (edge : State → State → Prop) : ℕ → State → State → Prop
  | 0,x,y => x=y
  | n+1,x,y => ∃z,exactLengthPath edge n x z ∧ edge z y

theorem actual_new_frontier_contains_only_previously_undiscovered_successors
    (edge : State → State → Prop) (seed : Set State) (n : ℕ) :
    frontier edge seed (n+1)=graphPost edge (frontier edge seed n)\visited edge seed n ∧
      visited edge seed (n+1)=visited edge seed n∪frontier edge seed (n+1) :=
  ⟨rfl,rfl⟩

theorem actual_frontier_is_visited_and_all_previous_visited_points_are_retained
    (edge : State → State → Prop) (seed : Set State) (n : ℕ) :
    frontier edge seed n⊆visited edge seed n ∧
      visited edge seed n⊆visited edge seed (n+1) := by
  constructor
  · cases n with
    | zero => exact Subset.rfl
    | succ n => exact fun _ h => Or.inr h
  · exact fun _ h => Or.inl h

theorem actual_all_current_frontier_successors_are_visited_in_the_next_round
    (edge : State → State → Prop) (seed : Set State) (n : ℕ) :
    graphPost edge (frontier edge seed n)⊆visited edge seed (n+1) := by
  intro y hy
  by_cases hv : y∈visited edge seed n
  · exact Or.inl hv
  · exact Or.inr ⟨hy,hv⟩

theorem actual_every_visited_point_has_already_been_expanded_or_is_in_the_frontier
    (edge : State → State → Prop) (seed : Set State) (n : ℕ) :
    ∀x∈visited edge seed n,∀y,edge x y →
      y∈visited edge seed n ∨ x∈frontier edge seed n := by
  induction n with
  | zero => exact fun _ hx _ _ => Or.inr hx
  | succ n ih =>
    intro x hx y he
    rcases hx with hx | hx
    · apply Or.inl
      rcases ih x hx y he with hy | hf
      · exact Or.inl hy
      · exact actual_all_current_frontier_successors_are_visited_in_the_next_round
          edge seed n ⟨x,hf,he⟩
    · exact Or.inr hx

theorem actual_layer_algorithm_matches_the_literal_seed_successor_set_iteration
    (edge : State → State → Prop) (seed : Set State) (n : ℕ) :
    visited edge seed n=iteration (graphStep edge seed) seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change visited edge seed n∪(graphPost edge (frontier edge seed n)\visited edge seed n)=
      graphStep edge seed (iteration (graphStep edge seed) seed n)
    rw [←ih]
    have hseed : seed⊆visited edge seed n := by
      rw [ih]
      exact actual_seed_is_contained_in_every_increasing_iterate
        (graphStep edge seed) (actual_directed_graph_successor_and_seed_step_are_monotone edge seed).2
        seed (fun _ h=>Or.inl h) n
    have hinc : visited edge seed n⊆graphStep edge seed (visited edge seed n) := by
      rw [ih]
      exact actual_increasing_chain_from_a_postfixed_seed
        (graphStep edge seed) (actual_directed_graph_successor_and_seed_step_are_monotone edge seed).2
        seed (fun _ h=>Or.inl h) n
    ext y
    constructor
    · rintro (hy | ⟨⟨x,hx,he⟩,_⟩)
      · exact hinc hy
      · exact Or.inr ⟨x,(actual_frontier_is_visited_and_all_previous_visited_points_are_retained
          edge seed n).1 hx,he⟩
    · rintro (hy | ⟨x,hx,he⟩)
      · exact Or.inl (hseed hy)
      · rcases actual_every_visited_point_has_already_been_expanded_or_is_in_the_frontier
          edge seed n x hx y he with hy | hf
        · exact Or.inl hy
        · by_cases hv : y∈visited edge seed n
          · exact Or.inl hv
          · exact Or.inr ⟨⟨x,hf,he⟩,hv⟩

theorem actual_breadth_first_layers_stop_at_true_graph_reachability_with_the_finite_budget
    [Finite State] (edge : State → State → Prop) (seed : Set State) :
    ∃n≤Nat.card State-seed.ncard,visited edge seed n=graphReach edge seed ∧
      frontier edge seed (n+1)=∅ ∧ ∀k,visited edge seed (n+k)=graphReach edge seed := by
  obtain ⟨n,hn,he,hafter⟩ := actual_finite_graph_set_expansion_stops_at_true_reachability edge seed
  have hv : visited edge seed n=graphReach edge seed :=
    (actual_layer_algorithm_matches_the_literal_seed_successor_set_iteration edge seed n).trans he
  refine ⟨n,hn,hv,?_,fun k=>
    (actual_layer_algorithm_matches_the_literal_seed_successor_set_iteration edge seed (n+k)).trans
      (hafter k)⟩
  apply eq_empty_iff_forall_notMem.mpr
  rintro y ⟨⟨x,hx,hedge⟩,hy⟩
  apply hy
  change y∈visited edge seed n
  rw [hv]
  have hxr : x∈graphReach edge seed := by
    rw [←hv]
    exact (actual_frontier_is_visited_and_all_previous_visited_points_are_retained edge seed n).1 hx
  obtain ⟨s,hs,hr⟩ := hxr
  exact ⟨s,hs,hr.tail hedge⟩

end SafeLearning.CompleteFoundationsBreadthFirstSearch
