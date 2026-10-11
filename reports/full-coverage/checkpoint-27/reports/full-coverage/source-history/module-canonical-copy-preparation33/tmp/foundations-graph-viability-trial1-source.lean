import SafeLearning.CompleteFoundationsFiniteSetIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsGraphViability
open CompleteFoundationsFiniteSetIteration

variable {State Input : Type*}

def controlledPre (F : State → Input → State) (allowed : State → Input → Prop)
    (Y : Set State) : Set State := {x | ∃u, allowed x u ∧ F x u∈Y}
def viabilityStep (F : State → Input → State) (allowed : State → Input → Prop)
    (Y : Set State) : Set State := Y∩controlledPre F allowed Y

theorem actual_existential_control_predecessor_is_monotone
    (F : State → Input → State) (allowed : State → Input → Prop) :
    Monotone (controlledPre F allowed) := by
  intro Y Z h x hx
  obtain ⟨u,hu,hy⟩ := hx
  exact ⟨u,hu,h hy⟩

theorem actual_literal_shrinking_viability_step_is_monotone
    (F : State → Input → State) (allowed : State → Input → Prop) :
    Monotone (viabilityStep F allowed) := by
  intro Y Z h x hx
  exact ⟨h hx.1,actual_existential_control_predecessor_is_monotone F allowed h hx.2⟩

theorem actual_viability_step_fixedpoint_iff_control_invariance
    (F : State → Input → State) (allowed : State → Input → Prop) (Y : Set State) :
    viabilityStep F allowed Y=Y ↔ Y⊆controlledPre F allowed Y := by
  constructor
  · intro h x hx
    have hy : x∈viabilityStep F allowed Y := by rwa [h]
    exact hy.2
  · intro h
    ext x
    exact ⟨fun hx=>hx.1,fun hx=>⟨hx,h hx⟩⟩

theorem actual_finite_viability_iteration_stops_at_the_greatest_invariant_subset
    [Finite State] (F : State → Input → State) (allowed : State → Input → Prop)
    (safe : Set State) :
    ∃n≤safe.ncard,
      IsGreatest {Y : Set State | Y⊆safe ∧ Y⊆controlledPre F allowed Y}
        (iteration (viabilityStep F allowed) safe n) ∧
      ∀k, iteration (viabilityStep F allowed) safe (n+k)=
        iteration (viabilityStep F allowed) safe n := by
  obtain ⟨n,hn,hgreat,hafter⟩ :=
    actual_final_decreasing_set_is_the_greatest_fixed_point_contained_in_the_seed
      (viabilityStep F allowed) (actual_literal_shrinking_viability_step_is_monotone F allowed)
      safe (fun _ h=>h.1)
  refine ⟨n,hn,⟨⟨hgreat.1.1,?_,⟩,?_⟩,hafter⟩
  · exact (actual_viability_step_fixedpoint_iff_control_invariance F allowed _).mp hgreat.1.2
  · intro Y hY
    exact hgreat.2 ⟨hY.1,(actual_viability_step_fixedpoint_iff_control_invariance F allowed Y).mpr hY.2⟩

theorem actual_control_invariance_constructs_an_entire_allowed_safe_trajectory
    (F : State → Input → State) (allowed : State → Input → Prop) (Y : Set State)
    (hY : Y⊆controlledPre F allowed Y) (initial : State) (hi : initial∈Y) :
    ∃x : ℕ→State, ∃u : ℕ→Input,
      x 0=initial ∧ ∀n, x n∈Y ∧ allowed (x n) (u n) ∧ x (n+1)=F (x n) (u n) := by
  classical
  let pick : Y→Input := fun y=>Classical.choose (hY y.property)
  have hp (y : Y) : allowed y (pick y) ∧ F y (pick y)∈Y :=
    Classical.choose_spec (hY y.property)
  let move : Y→Y := fun y=>⟨F y (pick y),(hp y).2⟩
  let z : ℕ→Y := fun n=>(move^[n]) ⟨initial,hi⟩
  refine ⟨fun n=>(z n).val,fun n=>pick (z n),rfl,?_⟩
  intro n
  refine ⟨(z n).property,(hp (z n)).1,?_⟩
  exact congrArg Subtype.val (Function.iterate_succ_apply' move n ⟨initial,hi⟩)

theorem actual_greatest_control_invariant_set_is_the_true_all_time_viability_kernel
    (F : State → Input → State) (allowed : State → Input → Prop)
    (safe kernel : Set State)
    (hk : IsGreatest {Y : Set State | Y⊆safe ∧ Y⊆controlledPre F allowed Y} kernel)
    (initial : State) :
    initial∈kernel ↔ ∃x : ℕ→State, ∃u : ℕ→Input,
      x 0=initial ∧ ∀n, x n∈safe ∧ allowed (x n) (u n) ∧ x (n+1)=F (x n) (u n) := by
  constructor
  · intro hi
    obtain ⟨x,u,h0,hpath⟩ :=
      actual_control_invariance_constructs_an_entire_allowed_safe_trajectory F allowed kernel hk.1.2 initial hi
    exact ⟨x,u,h0,fun n=>⟨hk.1.1 (hpath n).1,(hpath n).2⟩⟩
  · rintro ⟨x,u,h0,hpath⟩
    have hY : range x⊆safe ∧ range x⊆controlledPre F allowed (range x) := by
      constructor
      · rintro y ⟨n,rfl⟩
        exact (hpath n).1
      · rintro y ⟨n,rfl⟩
        exact ⟨u n,(hpath n).2.1,⟨n+1,(hpath n).2.2⟩⟩
    apply hk.2 hY
    exact ⟨0,h0⟩

def graphPost (edge : State → State → Prop) (Y : Set State) : Set State :=
  {y | ∃x∈Y,edge x y}
def graphReach (edge : State → State → Prop) (seed : Set State) : Set State :=
  {y | ∃x∈seed,Relation.ReflTransGen edge x y}
def graphStep (edge : State → State → Prop) (seed : Set State) (Y : Set State) :=
  seed∪graphPost edge Y

theorem actual_directed_graph_successor_and_seed_step_are_monotone
    (edge : State → State → Prop) (seed : Set State) :
    Monotone (graphPost edge) ∧ Monotone (graphStep edge seed) := by
  have hp : Monotone (graphPost edge) := by
    intro Y Z h y hy
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨x,h hx,he⟩
  exact ⟨hp,fun Y Z h y hy=>hy.elim (fun hs=>Or.inl hs) (fun hs=>Or.inr (hp h hs))⟩

theorem actual_true_graph_reachability_is_a_literal_seed_successor_fixedpoint
    (edge : State → State → Prop) (seed : Set State) :
    graphStep edge seed (graphReach edge seed)=graphReach edge seed := by
  ext y
  constructor
  · rintro (hy | ⟨x,⟨s,hs,hreach⟩,he⟩)
    · exact ⟨y,hy,Relation.ReflTransGen.refl⟩
    · exact ⟨s,hs,hreach.tail he⟩
  · rintro ⟨s,hs,hreach⟩
    rcases hreach.cases_tail with he | ⟨x,hx,he⟩
    · exact Or.inl (he ▸ hs)
    · exact Or.inr ⟨x,⟨s,hs,hx⟩,he⟩

theorem actual_true_graph_reachability_is_the_least_successor_closed_seed_superset
    (edge : State → State → Prop) (seed : Set State) :
    IsLeast {Y : Set State | seed⊆Y ∧ graphPost edge Y⊆Y} (graphReach edge seed) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x hx
    exact ⟨x,hx,Relation.ReflTransGen.refl⟩
  · rintro y ⟨x,⟨s,hs,hreach⟩,he⟩
    exact ⟨s,hs,hreach.tail he⟩
  · intro Y hY y hy
    obtain ⟨s,hs,hreach⟩ := hy
    have hpres : ∀{a b}, Relation.ReflTransGen edge a b → a∈Y → b∈Y := by
      intro a b hab
      induction hab with
      | refl => exact id
      | @tail b c hbc he ih =>
        intro ha
        exact hY.2 ⟨b,ih ha,he⟩
    exact hpres hreach (hY.1 hs)

theorem actual_finite_graph_set_expansion_stops_at_true_reachability
    [Finite State] (edge : State → State → Prop) (seed : Set State) :
    ∃n≤Nat.card State-seed.ncard,
      iteration (graphStep edge seed) seed n=graphReach edge seed ∧
      ∀k, iteration (graphStep edge seed) seed (n+k)=graphReach edge seed := by
  obtain ⟨n,hn,hleast,hafter⟩ :=
    actual_final_increasing_set_is_the_least_fixed_point_containing_the_seed
      (graphStep edge seed) (actual_directed_graph_successor_and_seed_step_are_monotone edge seed).2
      seed (fun _ h=>Or.inl h)
  have hclosed : graphPost edge (iteration (graphStep edge seed) seed n)⊆
      iteration (graphStep edge seed) seed n := by
    intro y hy
    have hh : y∈graphStep edge seed (iteration (graphStep edge seed) seed n) := Or.inr hy
    rwa [hleast.1.2] at hh
  have hreach := actual_true_graph_reachability_is_the_least_successor_closed_seed_superset edge seed
  have hleft := hreach.2 ⟨hleast.1.1,hclosed⟩
  have hright := hleast.2 ⟨hreach.1.1,
    actual_true_graph_reachability_is_a_literal_seed_successor_fixedpoint edge seed⟩
  have he : iteration (graphStep edge seed) seed n=graphReach edge seed := Set.Subset.antisymm hright hleft
  exact ⟨n,hn,he,fun k=>(hafter k).trans he⟩

end SafeLearning.CompleteFoundationsGraphViability
