import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteFoundationsFiniteReachability
open scoped BigOperators

def grow {α : Type*} [Fintype α] [DecidableEq α]
    (f : α→ℝ) (distance : α→α→ℝ) (epsilon : ℝ) (S : Finset α) : Finset α :=
  S ∪ Finset.univ.filter (fun x=>∃ y∈S,epsilon+distance x y ≤ f y)

theorem actual_grow_extensive {α : Type*} [Fintype α] [DecidableEq α]
    (f : α→ℝ) (distance : α→α→ℝ) (epsilon : ℝ) (S : Finset α) :
    S⊆grow f distance epsilon S := Finset.subset_union_left

theorem actual_grow_monotone {α : Type*} [Fintype α] [DecidableEq α]
    (f : α→ℝ) (distance : α→α→ℝ) (epsilon : ℝ) :
    Monotone (grow f distance epsilon) := by
  intro S T hST x hx
  rcases Finset.mem_union.mp hx with hs | hw
  · exact Finset.mem_union_left _ (hST hs)
  · obtain ⟨y,hy,he⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hST hy,he⟩)

theorem actual_grow_error_antitone {α : Type*} [Fintype α] [DecidableEq α]
    (f : α→ℝ) (distance : α→α→ℝ) (S : Finset α) {a b : ℝ} (hab : a≤b) :
    grow f distance b S⊆grow f distance a S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hs | hw
  · exact Finset.mem_union_left _ hs
  · obtain ⟨y,hy,he⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,y,hy,by linarith⟩)

theorem actual_finite_strict_increase_budget {α : Type*} [Fintype α]
    (S : ℕ→Finset α) (N : ℕ) (h : ∀ n<N,S n⊂S (n+1)) :
    N+(S 0).card≤Fintype.card α := by
  have hc : ∀ n≤N,n+(S 0).card≤(S n).card := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hp := ih (by omega)
      have hg := Finset.card_lt_card (h n (by omega))
      omega
  exact (hc N le_rfl).trans (Finset.card_le_univ _)

def fitness : Fin 9→ℝ := ![9/5,23/10,7/5,12/5,7/5,12/5,7/5,2/5,7/5]
def distance (x y : Fin 9) : ℝ := |(x.val:ℝ)-(y.val:ℝ)|
def sourceGrow (epsilon : ℝ) : Finset (Fin 9)→Finset (Fin 9) := grow fitness distance epsilon
def sourceIteration (epsilon : ℝ) (n : ℕ) : Finset (Fin 9) := (sourceGrow epsilon)^[n] {0}
def sourceClosure (epsilon : ℝ) : Set (Fin 9) := {x | ∃ n,x∈sourceIteration epsilon n}

theorem actual_iteration_succ (epsilon : ℝ) (n : ℕ) :
    sourceIteration epsilon (n+1)=sourceGrow epsilon (sourceIteration epsilon n) := by
  simp only [sourceIteration,Function.iterate_succ_apply']

theorem actual_source_certificate (epsilon : ℝ) (x y : Fin 9) :
    epsilon+distance x y≤fitness y ↔ fitness y-epsilon-|(x.val:ℝ)-(y.val:ℝ)|≥0 := by
  unfold distance
  constructor <;> intro h <;> linarith

theorem actual_half_error_iterates :
    sourceGrow (1/2) {0}={0,1} ∧ sourceGrow (1/2) {0,1}={0,1,2} ∧
    sourceGrow (1/2) {0,1,2}={0,1,2} := by
  constructor
  · ext x;fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]
  · constructor
    · ext x;fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]
    · ext x;fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]

theorem actual_half_error_stabilized (n : ℕ) : sourceIteration (1/2) (n+2)={0,1,2} := by
  have htwo : sourceIteration (1/2) 2={0,1,2} := by
    simp only [sourceIteration,Function.iterate_succ_apply,Function.iterate_zero_apply]
    rw [actual_half_error_iterates.1,actual_half_error_iterates.2.1]
  induction n with
  | zero => exact htwo
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,actual_iteration_succ,ih,actual_half_error_iterates.2.2]

theorem actual_half_error_closure : sourceClosure (1/2)={0,1,2} := by
  ext x
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => simp only [sourceIteration,Function.iterate_zero_apply,Finset.mem_singleton] at hn
              simp only [Set.mem_insert_iff,Set.mem_singleton_iff];exact Or.inl hn
    | succ n =>
      cases n with
      | zero =>
        have he : sourceIteration (1/2) 1={0,1} := actual_half_error_iterates.1
        rw [he] at hn
        simp only [Finset.mem_insert,Finset.mem_singleton] at hn
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff];tauto
      | succ n =>
        rw [show n+1+1=n+2 by omega,actual_half_error_stabilized] at hn
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using hn
  · intro hx
    refine ⟨2,?_⟩
    rw [show (2:ℕ)=0+2 by rfl,actual_half_error_stabilized]
    simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using hx

theorem actual_half_error_two_strict_increases :
    sourceIteration (1/2) 0⊂sourceIteration (1/2) 1 ∧
    sourceIteration (1/2) 1⊂sourceIteration (1/2) 2 ∧
    (Fintype.card (Fin 9)-(sourceIteration (1/2) 0).card)=8 ∧ (2:ℕ)≤8 := by
  have h0 : sourceIteration (1/2) 0={0} := rfl
  have h1 : sourceIteration (1/2) 1={0,1} := actual_half_error_iterates.1
  have h2 := actual_half_error_stabilized 0
  rw [h0,h1,h2]
  decide

theorem actual_zero_error_iterates :
    sourceGrow 0 {0}={0,1} ∧ sourceGrow 0 {0,1}={0,1,2,3} ∧
    sourceGrow 0 {0,1,2,3}={0,1,2,3,4,5} ∧
    sourceGrow 0 {0,1,2,3,4,5}={0,1,2,3,4,5,6,7} ∧
    sourceGrow 0 {0,1,2,3,4,5,6,7}={0,1,2,3,4,5,6,7} := by
  repeat' constructor
  all_goals ext x;fin_cases x <;> norm_num [sourceGrow,grow,fitness,distance,Finset.mem_filter]

theorem actual_zero_error_stabilized (n : ℕ) :
    sourceIteration 0 (n+4)={0,1,2,3,4,5,6,7} := by
  have hfour : sourceIteration 0 4={0,1,2,3,4,5,6,7} := by
    simp only [sourceIteration,Function.iterate_succ_apply,Function.iterate_zero_apply]
    rw [actual_zero_error_iterates.1,actual_zero_error_iterates.2.1,
      actual_zero_error_iterates.2.2.1,actual_zero_error_iterates.2.2.2.1]
  induction n with
  | zero => exact hfour
  | succ n ih =>
    rw [show n+1+4=(n+4)+1 by omega,actual_iteration_succ,ih,actual_zero_error_iterates.2.2.2.2]

theorem actual_zero_error_closure : sourceClosure 0={0,1,2,3,4,5,6,7} := by
  ext x
  constructor
  · rintro ⟨n,hn⟩
    by_cases hb : n<4
    · interval_cases n <;>
        simp only [sourceIteration,Function.iterate_succ_apply,Function.iterate_zero_apply] at hn
      all_goals try rw [actual_zero_error_iterates.1] at hn
      all_goals try rw [actual_zero_error_iterates.2.1] at hn
      all_goals try rw [actual_zero_error_iterates.2.2.1] at hn
      all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at hn
      all_goals simp only [Set.mem_insert_iff,Set.mem_singleton_iff];tauto
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 4≤n by omega)
      simpa [add_comm,actual_zero_error_stabilized] using hn
  · intro hx;refine ⟨4,?_⟩;simpa [actual_zero_error_stabilized 0] using hx

theorem actual_closure_cardinality_shrink :
    (sourceClosure 0).ncard=8 ∧ (sourceClosure (1/2)).ncard=3 ∧
    sourceClosure (1/2)⊂sourceClosure 0 := by
  rw [actual_zero_error_closure,actual_half_error_closure]
  norm_num [Set.ncard_insert_of_notMem,Set.ncard_singleton]
  constructor
  · intro x hx;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢;tauto
  · intro h
    have h3 := h (by norm_num : (3:Fin 9)∈({0,1,2,3,4,5,6,7}:Set (Fin 9)))
    norm_num at h3

theorem actual_gateway_and_dip :
    fitness 1-distance 3 1=3/10 ∧ (3/10:ℝ)<1/2 ∧
    fitness 2-1/2-distance 3 2= -1/10 ∧
    3∈sourceClosure 0 ∧ 3∉sourceClosure (1/2) ∧
    8∉sourceClosure 0 := by
  rw [actual_zero_error_closure,actual_half_error_closure]
  norm_num [fitness,distance]

end SafeLearning.CompleteFoundationsFiniteReachability
