import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsFiniteSetIteration

def iteration {α : Type*} (Phi : Set α → Set α) (seed : Set α) : ℕ → Set α
  | 0 => seed
  | n+1 => Phi (iteration Phi seed n)

theorem actual_increasing_chain_from_a_postfixed_seed {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed : Set α)
    (hseed : seed ⊆ Phi seed) :
    ∀ n, iteration Phi seed n ⊆ iteration Phi seed (n+1) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih => exact hmono ih

theorem actual_seed_is_contained_in_every_increasing_iterate {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed : Set α)
    (hseed : seed ⊆ Phi seed) (n : ℕ) : seed ⊆ iteration Phi seed n := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact ih.trans (actual_increasing_chain_from_a_postfixed_seed Phi hmono seed hseed n)

theorem actual_finite_strict_increase_budget {α : Type*} [Finite α]
    (S : ℕ → Set α) (N : ℕ) (hstrict : ∀ n < N, S n ⊂ S (n+1)) :
    N + (S 0).ncard ≤ Nat.card α := by
  have hcard : ∀ n ≤ N, n + (S 0).ncard ≤ (S n).ncard := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := ih (by omega)
      have hs := Set.ncard_lt_ncard (hstrict n (by omega))
      omega
  exact (hcard N le_rfl).trans (Set.ncard_le_card _)

theorem actual_equality_at_one_step_makes_every_later_iterate_identical {α : Type*}
    (Phi : Set α → Set α) (seed : Set α) (n : ℕ)
    (hfixed : iteration Phi seed (n+1) = iteration Phi seed n) :
    ∀ k, iteration Phi seed (n+k) = iteration Phi seed n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    change Phi (iteration Phi seed (n+k)) = iteration Phi seed n
    rw [ih]
    exact hfixed

theorem actual_increasing_iteration_stops_within_the_unused_point_budget
    {α : Type*} [Finite α] (Phi : Set α → Set α) (hmono : Monotone Phi)
    (seed : Set α) (hseed : seed ⊆ Phi seed) :
    ∃ n ≤ Nat.card α - seed.ncard,
      iteration Phi seed (n+1) = iteration Phi seed n := by
  by_contra hn
  push_neg at hn
  have hs : ∀ n < (Nat.card α - seed.ncard)+1,
      iteration Phi seed n ⊂ iteration Phi seed (n+1) := by
    intro n hbound
    apply Set.ssubset_iff_subset_ne.mpr
    exact ⟨actual_increasing_chain_from_a_postfixed_seed Phi hmono seed hseed n,
      Ne.symm (hn n (by omega))⟩
  have hc := actual_finite_strict_increase_budget (iteration Phi seed)
    ((Nat.card α - seed.ncard)+1) hs
  change (Nat.card α-seed.ncard)+1+seed.ncard ≤ Nat.card α at hc
  have hseedcard := Set.ncard_le_card seed
  omega

theorem actual_every_prefixed_superset_bounds_all_increasing_iterates {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed target : Set α)
    (hseed : seed ⊆ target) (htarget : Phi target ⊆ target) :
    ∀ n, iteration Phi seed n ⊆ target := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih => exact (hmono ih).trans htarget

theorem actual_final_increasing_set_is_the_least_fixed_point_containing_the_seed
    {α : Type*} [Finite α] (Phi : Set α → Set α) (hmono : Monotone Phi)
    (seed : Set α) (hseed : seed ⊆ Phi seed) :
    ∃ n ≤ Nat.card α - seed.ncard,
      IsLeast {target : Set α | seed ⊆ target ∧ Phi target = target}
        (iteration Phi seed n) ∧
      ∀ k, iteration Phi seed (n+k) = iteration Phi seed n := by
  obtain ⟨n,hn,hfix⟩ := actual_increasing_iteration_stops_within_the_unused_point_budget
    Phi hmono seed hseed
  refine ⟨n,hn,⟨⟨actual_seed_is_contained_in_every_increasing_iterate
    Phi hmono seed hseed n,hfix⟩,?_⟩,
    actual_equality_at_one_step_makes_every_later_iterate_identical Phi seed n hfix⟩
  intro target ht
  exact actual_every_prefixed_superset_bounds_all_increasing_iterates
    Phi hmono seed target ht.1 (le_of_eq ht.2) n

theorem actual_decreasing_chain_from_a_prefixed_seed {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed : Set α)
    (hseed : Phi seed ⊆ seed) :
    ∀ n, iteration Phi seed (n+1) ⊆ iteration Phi seed n := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih => exact hmono ih

theorem actual_every_decreasing_iterate_is_contained_in_the_seed {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed : Set α)
    (hseed : Phi seed ⊆ seed) (n : ℕ) : iteration Phi seed n ⊆ seed := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact (actual_decreasing_chain_from_a_prefixed_seed Phi hmono seed hseed n).trans ih

theorem actual_finite_strict_decrease_budget {α : Type*} [Finite α]
    (S : ℕ → Set α) (N : ℕ) (hstrict : ∀ n < N, S (n+1) ⊂ S n) :
    N + (S N).ncard ≤ (S 0).ncard := by
  have hcard : ∀ n ≤ N, n + (S n).ncard ≤ (S 0).ncard := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := ih (by omega)
      have hs := Set.ncard_lt_ncard (hstrict n (by omega))
      omega
  exact hcard N le_rfl

theorem actual_decreasing_iteration_stops_within_the_initial_point_budget
    {α : Type*} [Finite α] (Phi : Set α → Set α) (hmono : Monotone Phi)
    (seed : Set α) (hseed : Phi seed ⊆ seed) :
    ∃ n ≤ seed.ncard, iteration Phi seed (n+1) = iteration Phi seed n := by
  by_contra hn
  push_neg at hn
  have hs : ∀ n < seed.ncard+1,
      iteration Phi seed (n+1) ⊂ iteration Phi seed n := by
    intro n hbound
    apply Set.ssubset_iff_subset_ne.mpr
    exact ⟨actual_decreasing_chain_from_a_prefixed_seed Phi hmono seed hseed n,
      hn n (by omega)⟩
  have hc := actual_finite_strict_decrease_budget (iteration Phi seed) (seed.ncard+1) hs
  change seed.ncard+1+(iteration Phi seed (seed.ncard+1)).ncard ≤ seed.ncard at hc
  omega

theorem actual_every_postfixed_subset_is_contained_in_all_decreasing_iterates {α : Type*}
    (Phi : Set α → Set α) (hmono : Monotone Phi) (seed target : Set α)
    (hseed : target ⊆ seed) (htarget : target ⊆ Phi target) :
    ∀ n, target ⊆ iteration Phi seed n := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih => exact htarget.trans (hmono ih)

theorem actual_final_decreasing_set_is_the_greatest_fixed_point_contained_in_the_seed
    {α : Type*} [Finite α] (Phi : Set α → Set α) (hmono : Monotone Phi)
    (seed : Set α) (hseed : Phi seed ⊆ seed) :
    ∃ n ≤ seed.ncard,
      IsGreatest {target : Set α | target ⊆ seed ∧ Phi target = target}
        (iteration Phi seed n) ∧
      ∀ k, iteration Phi seed (n+k) = iteration Phi seed n := by
  obtain ⟨n,hn,hfix⟩ := actual_decreasing_iteration_stops_within_the_initial_point_budget
    Phi hmono seed hseed
  refine ⟨n,hn,⟨⟨actual_every_decreasing_iterate_is_contained_in_the_seed
    Phi hmono seed hseed n,hfix⟩,?_⟩,
    actual_equality_at_one_step_makes_every_later_iterate_identical Phi seed n hfix⟩
  intro target ht
  exact actual_every_postfixed_subset_is_contained_in_all_decreasing_iterates
    Phi hmono seed target ht.1 (le_of_eq ht.2.symm) n

end SafeLearning.CompleteFoundationsFiniteSetIteration
