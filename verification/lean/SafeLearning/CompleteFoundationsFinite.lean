import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteFoundationsFinite

theorem finite_orbit_collision {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card α ∧ f^[i] x=f^[j] x := by
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card α+1) => f^[k.val] x) (by simp)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i.val,j.val,hij,by omega,he⟩
  · exact ⟨j.val,i.val,hji,by omega,he.symm⟩

theorem orbit_reduce_at_collision {α : Type*} (f : α → α) (x : α) (i j n : ℕ)
    (hi : i < j) (hj : j ≤ n) (he : f^[i] x=f^[j] x) :
    f^[n] x=f^[n-j+i] x ∧ n-j+i<n := by
  constructor
  · calc
      f^[n] x=f^[n-j] (f^[j] x) := by rw [← Function.iterate_add_apply]; congr 1; omega
      _ = f^[n-j] (f^[i] x) := by rw [← he]
      _ = f^[n-j+i] x := (Function.iterate_add_apply _ _ _ _).symm
  · omega

theorem finite_orbit_early_occurrence {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∀ n : ℕ, ∃ k < Fintype.card α, f^[n] x=f^[k] x := by
  obtain ⟨i,j,hi,hj,he⟩ := finite_orbit_collision f x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < Fintype.card α
    · exact ⟨n,hn,rfl⟩
    · obtain ⟨hr,hm⟩ := orbit_reduce_at_collision f x i j n hi (by omega) he
      obtain ⟨k,hk,h⟩ := ih (n-j+i) hm
      exact ⟨k,hk,hr.trans h⟩

theorem finite_state_check_all_time {α : Type*} [Fintype α]
    (f : α → α) (x : α) (P : α → Prop)
    (h : ∀ k < Fintype.card α, P (f^[k] x)) :
    ∀ n, P (f^[n] x) := by
  intro n
  obtain ⟨k,hk,he⟩ := finite_orbit_early_occurrence f x n
  rw [he]; exact h k hk

def fourState : Fin 4 → Fin 4 := ![1,2,1,3]

theorem four_state_first_five :
    fourState^[0] 0=0 ∧ fourState^[1] 0=1 ∧ fourState^[2] 0=2 ∧
    fourState^[3] 0=1 ∧ fourState^[4] 0=2 := by decide

theorem four_state_never_failure : ∀ n, fourState^[n] 0 ≠ 3 := by
  apply finite_state_check_all_time fourState 0 (fun x => x ≠ 3)
  intro k hk
  have hfour : k < 4 := by simpa using hk
  interval_cases k <;> decide

theorem changing_rule_counterexample :
    let x : ℕ → Fin 4 := fun n => if n<4 then 0 else 3
    let f : ℕ → Fin 4 → Fin 4 := fun n _ => if n<3 then 0 else 3
    (∀ n, x (n+1)=f n (x n)) ∧ (∀ n<4, x n ≠ 3) ∧ x 4=3 := by
  dsimp
  refine ⟨?_,?_,by decide⟩
  · intro n; split_ifs <;> simp_all <;> omega
  · intro n hn; simp [hn]

theorem increasing_cardinality_budget {α : Type*} [Fintype α]
    (S : ℕ → Finset α) (N : ℕ) (h : ∀ n<N, S n ⊂ S (n+1)) :
    N+ (S 0).card ≤ Fintype.card α := by
  have hh : ∀ n≤N, n+(S 0).card ≤ (S n).card := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := ih (by omega)
      have hs := Finset.card_lt_card (h n (by omega))
      omega
  exact (hh N le_rfl).trans (Finset.card_le_univ _)

end SafeLearning.CompleteFoundationsFinite
