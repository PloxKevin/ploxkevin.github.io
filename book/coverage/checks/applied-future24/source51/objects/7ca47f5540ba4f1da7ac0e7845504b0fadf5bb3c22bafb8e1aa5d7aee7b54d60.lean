import SafeLearning.CompleteFoundationsFiniteDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsFiniteDynamicsConsequences

theorem actual_periodic_tail_repeats_exactly_a_finite_block
    {X : Type*} (x : ℕ → X) (i j : ℕ) (hij : i<j)
    (hperiod : ∀ t, i≤t → x (t+(j-i))=x t) :
    ∀ n, i≤n → ∃ k, i≤k ∧ k<j ∧ x k=x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hin
    by_cases hnj : n<j
    · exact ⟨n,hin,hnj,rfl⟩
    · have hp : 0<j-i := by omega
      have hm : i≤n-(j-i) := by omega
      have hlt : n-(j-i)<n := by omega
      obtain ⟨k,hik,hkj,hk⟩:=ih (n-(j-i)) hlt hm
      have he := hperiod (n-(j-i)) hm
      have hn : (n-(j-i))+(j-i)=n := by omega
      rw [hn] at he
      exact ⟨k,hik,hkj,hk.trans he.symm⟩

theorem actual_finite_deterministic_loop_has_the_literal_repeating_prefix_block
    {X : Type*} [Fintype X] (F : X→X) (x : ℕ→X)
    (hnext : ∀ n,x (n+1)=F (x n)) :
    ∃ i j, i<j ∧ j≤Fintype.card X ∧ j-1≤Fintype.card X-1 ∧
      x i=x j ∧ (∀ m,x (i+m)=x (j+m)) ∧
      (∀ n,i≤n→∃ k,i≤k ∧ k<j ∧ x k=x n) := by
  obtain ⟨i,j,hij,hcard,he,hfuture,hperiod⟩ :=
    CompleteFoundationsFiniteDynamics.actual_finite_deterministic_trajectory_has_a_positive_periodic_tail F x hnext
  exact ⟨i,j,hij,hcard,by omega,he,hfuture,
    actual_periodic_tail_repeats_exactly_a_finite_block x i j hij hperiod⟩

theorem actual_strong_induction_uses_all_statements_through_the_previous_index
    (P : ℕ→Prop) (hzero : P 0)
    (hstep : ∀ t,(∀ k,k≤t→P k)→P (t+1)) : ∀ t,P t := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero
    | succ n => exact hstep n (fun k hk=>ih k (by omega))

end SafeLearning.CompleteFoundationsFiniteDynamicsConsequences
