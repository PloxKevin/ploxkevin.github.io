import SafeLearning.CompleteFoundationsGraphViability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsSafetySetOperators
open CompleteFoundationsFiniteSetIteration CompleteFoundationsGraphViability

variable {State Constraint Input Label : Type*}

def commonReach (certificate : Constraint → State → State → Prop) (old : Set State) : Set State :=
  old ∪ {x | ∃ anchor ∈ old, ∀ i, certificate i anchor x}

def separateReach (certificate : Constraint → State → State → Prop) (old : Set State) : Set State :=
  old ∪ {x | ∀ i, ∃ anchor ∈ old, certificate i anchor x}

theorem actual_common_and_separate_certificate_operators_are_inflationary
    (certificate : Constraint → State → State → Prop) (old : Set State) :
    old ⊆ commonReach certificate old ∧ old ⊆ separateReach certificate old :=
  ⟨fun _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem actual_common_and_separate_certificate_operators_are_monotone
    (certificate : Constraint → State → State → Prop) :
    Monotone (commonReach certificate) ∧ Monotone (separateReach certificate) := by
  constructor
  · intro A B h x hx
    rcases hx with hx | ⟨anchor, ha, hc⟩
    · exact Or.inl (h hx)
    · exact Or.inr ⟨anchor, h ha, hc⟩
  · intro A B h x hx
    rcases hx with hx | hc
    · exact Or.inl (h hx)
    · apply Or.inr
      intro i
      obtain ⟨anchor, ha, hi⟩ := hc i
      exact ⟨anchor, h ha, hi⟩

theorem actual_common_witness_expansion_is_contained_in_separate_witness_expansion
    (certificate : Constraint → State → State → Prop) (old : Set State) :
    commonReach certificate old ⊆ separateReach certificate old := by
  intro x hx
  rcases hx with hx | ⟨anchor, ha, hc⟩
  · exact Or.inl hx
  · exact Or.inr (fun i => ⟨anchor, ha, hc i⟩)

theorem actual_finite_common_and_separate_closures_stop_at_least_fixed_points
    [Finite State] (certificate : Constraint → State → State → Prop) (seed : Set State) :
    (∃ n ≤ Nat.card State - seed.ncard,
      IsLeast {Y : Set State | seed ⊆ Y ∧ commonReach certificate Y = Y}
        (iteration (commonReach certificate) seed n) ∧
      ∀ k, iteration (commonReach certificate) seed (n+k) =
        iteration (commonReach certificate) seed n) ∧
    (∃ n ≤ Nat.card State - seed.ncard,
      IsLeast {Y : Set State | seed ⊆ Y ∧ separateReach certificate Y = Y}
        (iteration (separateReach certificate) seed n) ∧
      ∀ k, iteration (separateReach certificate) seed (n+k) =
        iteration (separateReach certificate) seed n) := by
  have hm := actual_common_and_separate_certificate_operators_are_monotone certificate
  exact ⟨actual_final_increasing_set_is_the_least_fixed_point_containing_the_seed
    _ hm.1 seed (actual_common_and_separate_certificate_operators_are_inflationary certificate seed).1,
    actual_final_increasing_set_is_the_least_fixed_point_containing_the_seed
    _ hm.2 seed (actual_common_and_separate_certificate_operators_are_inflationary certificate seed).2⟩

theorem actual_every_common_witness_iterate_is_contained_in_the_separate_witness_iterate
    (certificate : Constraint → State → State → Prop) (seed : Set State) :
    ∀ n, iteration (commonReach certificate) seed n ⊆ iteration (separateReach certificate) seed n := by
  intro n
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    exact (actual_common_witness_expansion_is_contained_in_separate_witness_expansion
      certificate _).trans
      ((actual_common_and_separate_certificate_operators_are_monotone certificate).2 ih)

theorem actual_common_witness_union_closure_is_contained_in_the_separate_witness_union_closure
    (certificate : Constraint → State → State → Prop) (seed : Set State) :
    (⋃ n, iteration (commonReach certificate) seed n) ⊆
      ⋃ n, iteration (separateReach certificate) seed n := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨n,
    actual_every_common_witness_iterate_is_contained_in_the_separate_witness_iterate certificate seed n hn⟩

def returnStep (allowed : Set State) (edge : State → State → Prop) (target : Set State) : Set State :=
  target ∪ {x | x ∈ allowed ∧ ∃ y ∈ target, edge x y}

theorem actual_return_operator_is_the_true_reverse_edge_expansion
    (allowed : Set State) (edge : State → State → Prop) (target : Set State) :
    returnStep allowed edge target =
      target ∪ graphPost (fun y x => x ∈ allowed ∧ edge x y) target := by
  ext x
  constructor
  · rintro (hx | ⟨ha, y, hy, he⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy, ha, he⟩
  · rintro (hx | ⟨y, hy, ha, he⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨ha, y, hy, he⟩

theorem actual_return_operator_keeps_its_target_and_is_monotone
    (allowed : Set State) (edge : State → State → Prop) :
    (∀ target, target ⊆ returnStep allowed edge target) ∧ Monotone (returnStep allowed edge) := by
  constructor
  · exact fun _ _ h => Or.inl h
  · intro A B h x hx
    rcases hx with hx | ⟨ha, y, hy, he⟩
    · exact Or.inl (h hx)
    · exact Or.inr ⟨ha, y, h hy, he⟩

theorem actual_finite_return_iteration_stops_at_its_least_fixed_point
    [Finite State] (allowed : Set State) (edge : State → State → Prop) (target : Set State) :
    ∃ n ≤ Nat.card State - target.ncard,
      IsLeast {Y : Set State | target ⊆ Y ∧ returnStep allowed edge Y = Y}
        (iteration (returnStep allowed edge) target n) ∧
      ∀ k, iteration (returnStep allowed edge) target (n+k) =
        iteration (returnStep allowed edge) target n := by
  have hm := actual_return_operator_keeps_its_target_and_is_monotone allowed edge
  exact actual_final_increasing_set_is_the_least_fixed_point_containing_the_seed
    _ hm.2 target (hm.1 target)

def cpreBefore (successor : State → Input → Label → State) (Y : Set State) : Set State :=
  {x | ∃ action, ∀ label, successor x action label ∈ Y}
def cpreAfter (successor : State → Input → Label → State) (Y : Set State) : Set State :=
  {x | ∀ label, ∃ action, successor x action label ∈ Y}
def safetyStep (safe : Set State) (pre : Set State → Set State) (Y : Set State) : Set State :=
  safe ∩ pre Y

theorem actual_both_move_order_control_predecessors_are_monotone
    (successor : State → Input → Label → State) :
    Monotone (cpreBefore successor) ∧ Monotone (cpreAfter successor) := by
  constructor
  · intro Y Z h x hx
    obtain ⟨action, ha⟩ := hx
    exact ⟨action, fun label => h (ha label)⟩
  · intro Y Z h x hx label
    obtain ⟨action, ha⟩ := hx label
    exact ⟨action, h ha⟩

theorem actual_action_before_revelation_is_a_stronger_predecessor
    (successor : State → Input → Label → State) (Y : Set State) :
    cpreBefore successor Y ⊆ cpreAfter successor Y := by
  rintro x ⟨action, ha⟩ label
  exact ⟨action, ha label⟩

theorem actual_safe_now_and_control_predecessor_operator_is_monotone
    (safe : Set State) (pre : Set State → Set State) (hm : Monotone pre) :
    Monotone (safetyStep safe pre) := by
  intro Y Z h x hx
  exact ⟨hx.1, hm h hx.2⟩

theorem actual_finite_safety_game_iteration_stops_at_a_greatest_fixed_point
    [Finite State] (safe : Set State) (pre : Set State → Set State) (hm : Monotone pre) :
    ∃ n ≤ safe.ncard,
      IsGreatest {Y : Set State | Y ⊆ safe ∧ safetyStep safe pre Y = Y}
        (iteration (safetyStep safe pre) safe n) ∧
      ∀ k, iteration (safetyStep safe pre) safe (n+k) =
        iteration (safetyStep safe pre) safe n := by
  exact actual_final_decreasing_set_is_the_greatest_fixed_point_contained_in_the_seed
    _ (actual_safe_now_and_control_predecessor_operator_is_monotone safe pre hm)
    safe (fun _ h => h.1)

theorem actual_safety_game_fixed_points_are_safe_control_invariant_sets
    (safe Y : Set State) (pre : Set State → Set State) :
    safetyStep safe pre Y = Y → Y ⊆ safe ∧ Y ⊆ pre Y := by
  intro he
  constructor
  · intro x hx
    have h : x ∈ safetyStep safe pre Y := by rwa [he]
    exact h.1
  · intro x hx
    have h : x ∈ safetyStep safe pre Y := by rwa [he]
    exact h.2

theorem actual_finite_safety_game_final_set_is_the_greatest_safe_control_invariant_set
    [Finite State] (safe : Set State) (pre : Set State → Set State) (hm : Monotone pre) :
    ∃ n ≤ safe.ncard,
      IsGreatest {Y : Set State | Y ⊆ safe ∧ Y ⊆ pre Y}
        (iteration (safetyStep safe pre) safe n) ∧
      safetyStep safe pre (iteration (safetyStep safe pre) safe n) =
        iteration (safetyStep safe pre) safe n ∧
      ∀ k, iteration (safetyStep safe pre) safe (n+k) =
        iteration (safetyStep safe pre) safe n := by
  obtain ⟨n, hn, hg, ha⟩ :=
    actual_finite_safety_game_iteration_stops_at_a_greatest_fixed_point safe pre hm
  refine ⟨n, hn, ⟨actual_safety_game_fixed_points_are_safe_control_invariant_sets
    safe _ pre hg.1.2, ?_⟩, hg.1.2, ha⟩
  intro Y hY
  exact actual_every_postfixed_subset_is_contained_in_all_decreasing_iterates
    (safetyStep safe pre) (actual_safe_now_and_control_predecessor_operator_is_monotone safe pre hm)
    safe Y hY.1 (fun _ hx => ⟨hY.1 hx, hY.2 hx⟩) n

theorem actual_before_predecessor_is_one_action_then_every_possible_successor
    (successor : State → Input → Label → State) (Y : Set State) :
    cpreBefore successor Y = {x | ∃ action, range (successor x action) ⊆ Y} := by
  ext x
  constructor
  · rintro ⟨action, ha⟩
    refine ⟨action, ?_⟩
    rintro z ⟨label, rfl⟩
    exact ha label
  · rintro ⟨action, ha⟩
    exact ⟨action, fun label => ha ⟨label, rfl⟩⟩

theorem actual_before_invariance_selects_one_safe_action_for_every_label
    (successor : State → Input → Label → State) (Y : Set State)
    (hinv : Y ⊆ cpreBefore successor Y) :
    ∃ action : Y → Input, ∀ x : Y, ∀ label, successor x (action x) label ∈ Y := by
  classical
  exact ⟨fun x => Classical.choose (hinv x.property),
    fun x => Classical.choose_spec (hinv x.property)⟩

theorem actual_after_invariance_selects_a_safe_action_after_each_revealed_label
    (successor : State → Input → Label → State) (Y : Set State)
    (hinv : Y ⊆ cpreAfter successor Y) :
    ∃ action : Y → Label → Input, ∀ x : Y, ∀ label,
      successor x (action x label) label ∈ Y := by
  classical
  exact ⟨fun x label => Classical.choose (hinv x.property label),
    fun x label => Classical.choose_spec (hinv x.property label)⟩

end SafeLearning.CompleteFoundationsSafetySetOperators
