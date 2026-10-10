import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsFiniteDynamics

variable {X : Type*} [Fintype X]

theorem actual_pigeonhole_repeated_state_in_the_first_cardinality_plus_one
    (x : ℕ → X) : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card X ∧ x i = x j := by
  classical
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card X + 1) => x k) (by simp)
  by_cases hij : i.val < j.val
  · exact ⟨i, j, hij, by omega, he⟩
  · have hji : j.val < i.val := by
      have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
      omega
    exact ⟨j, i, hji, by omega, he.symm⟩

theorem actual_determinism_propagates_a_repeated_state_to_every_future_time
    (F : X → X) (x : ℕ → X) (hnext : ∀ n, x (n+1)=F (x n))
    (i j : ℕ) (he : x i = x j) : ∀ m : ℕ, x (i+m)=x (j+m) := by
  intro m
  induction m with
  | zero => simpa using he
  | succ m ih =>
      change x ((i+m)+1)=x ((j+m)+1)
      rw [hnext, hnext, ih]

theorem actual_finite_deterministic_trajectory_has_a_positive_periodic_tail
    (F : X → X) (x : ℕ → X) (hnext : ∀ n, x (n+1)=F (x n)) :
    ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card X ∧ x i=x j ∧
      (∀ m : ℕ, x (i+m)=x (j+m)) ∧
      (∀ t : ℕ, i≤t → x (t+(j-i))=x t) := by
  obtain ⟨i,j,hij,hj,he⟩ := actual_pigeonhole_repeated_state_in_the_first_cardinality_plus_one x
  have hs := actual_determinism_propagates_a_repeated_state_to_every_future_time F x hnext i j he
  refine ⟨i,j,hij,hj,he,hs,?_⟩
  intro t ht
  have h := hs (t-i)
  have hi : i+(t-i)=t := by omega
  have hjt : j+(t-i)=t+(j-i) := by omega
  rw [hi,hjt] at h
  exact h.symm

theorem actual_every_visited_state_occurs_before_the_state_cardinality
    (F : X → X) (x : ℕ → X) (hnext : ∀ n, x (n+1)=F (x n)) :
    ∀ n : ℕ, ∃ k : ℕ, k < Fintype.card X ∧ x k=x n := by
  obtain ⟨i,j,hij,hj,he⟩ := actual_pigeonhole_repeated_state_in_the_first_cardinality_plus_one x
  have hs := actual_determinism_propagates_a_repeated_state_to_every_future_time F x hnext i j he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < Fintype.card X
    · exact ⟨n,hn,rfl⟩
    · have hjn : j ≤ n := by omega
      have hl : i+(n-j)<n := by omega
      obtain ⟨k,hk,he'⟩ := ih (i+(n-j)) hl
      have h := hs (n-j)
      have hjadd : j+(n-j)=n := by omega
      rw [hjadd] at h
      exact ⟨k,hk,he'.trans h⟩

theorem actual_finite_deterministic_failure_is_decidable_with_the_literal_horizon
    (F : X → X) (x : ℕ → X) (hnext : ∀ n, x (n+1)=F (x n)) (failure : Set X) :
    (∃ n : ℕ, x n ∈ failure) ↔ ∃ n : ℕ, n ≤ Fintype.card X-1 ∧ x n ∈ failure := by
  have hc : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x 0⟩
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk,he⟩ := actual_every_visited_state_occurs_before_the_state_cardinality F x hnext n
    exact ⟨k,by omega,by simpa [he] using hn⟩
  · rintro ⟨n,_,hn⟩; exact ⟨n,hn⟩

theorem actual_mathematical_induction_principle (P : ℕ → Prop)
    (hzero : P 0) (hstep : ∀ n, P n → P (n+1)) : ∀ n, P n := by
  intro n; induction n with
  | zero => exact hzero
  | succ n ih => exact hstep n ih

theorem actual_strong_induction_principle (P : ℕ → Prop)
    (hstep : ∀ n, (∀ k<n, P k) → P n) : ∀ n, P n := by
  intro n; induction n using Nat.strong_induction_on with
  | h n ih => exact hstep n ih

end SafeLearning.CompleteFoundationsFiniteDynamics
