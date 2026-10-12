import SafeLearning.CompleteFoundationsGraphViability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedViabilityFinitePractices20
open CompleteFoundationsGraphViability

def p1Next (s : Fin 3) (go : Bool) : Fin 3 :=
  if s=0 then if go then 1 else 0 else 2
def p1Safe : Set (Fin 3) := {s | s ≠ 2}
def p1Kernel : Set (Fin 3) := {0}
def allowed {S : Type*} (_ : S) (_ : Bool) : Prop := True

theorem actual_p1_safe_now_and_one_safe_successor_test (s : Fin 3) :
    (s∈p1Safe ∧ ∃a : Bool, p1Next s a∈p1Safe) ↔ s=0 := by
  fin_cases s <;> simp [p1Safe,p1Next] 

theorem actual_p1_kernel_is_the_greatest_control_invariant_subset :
    IsGreatest {Y : Set (Fin 3) | Y⊆p1Safe ∧ Y⊆controlledPre p1Next allowed Y} p1Kernel := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro s hs
    have h : s=0 := hs
    subst s
    simp [p1Safe]
  · intro s hs
    have h : s=0 := hs
    subst s
    exact ⟨false, trivial, by simp [p1Next,p1Kernel]⟩
  · rintro Y ⟨hYs,hY⟩ s hs
    obtain ⟨a,_,hnext⟩ := hY hs
    have h := (actual_p1_safe_now_and_one_safe_successor_test s).mp ⟨hYs hs, a, hYs hnext⟩
    exact h

theorem actual_p1_true_all_time_viability_iff_and_critical_action (initial : Fin 3) :
    ((∃x : ℕ→Fin 3, ∃a : ℕ→Bool,
      x 0=initial ∧ ∀n, x n∈p1Safe ∧ x (n+1)=p1Next (x n) (a n)) ↔ initial=0) ∧
    (∀a : Bool, p1Next 0 a∈p1Kernel ↔ a=false) ∧
    p1Next 0 true∈p1Safe ∧ p1Next 0 true∉p1Kernel := by
  have h := actual_greatest_control_invariant_set_is_the_true_all_time_viability_kernel
    p1Next allowed p1Safe p1Kernel actual_p1_kernel_is_the_greatest_control_invariant_subset initial
  refine ⟨?_,?_,by simp [p1Next,p1Safe],by simp [p1Next,p1Kernel]⟩
  · constructor
    · rintro ⟨x,a,h0,hpath⟩
      exact h.mpr ⟨x,a,h0,fun n=>⟨(hpath n).1,trivial,(hpath n).2⟩⟩
    · intro hi
      obtain ⟨x,a,h0,hpath⟩ := h.mp hi
      exact ⟨x,a,h0,fun n=>⟨(hpath n).1,(hpath n).2.2⟩⟩
  · intro a
    cases a <;> simp [p1Next,p1Kernel]

def p2Successor (a : Fin 5) : Fin 4 := ![0,0,1,2,3] a
def p2Kernel : Set (Fin 4) := {0,1}
def p2ViableActions : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun a=>p2Successor a∈p2Kernel)

theorem actual_p2_action_count_keeps_duplicate_successors :
    p2ViableActions={0,1,2} ∧ p2ViableActions.card=3 ∧
    (p2ViableActions.image p2Successor).card=2 ∧
    (p2ViableActions.card : ℝ)/(Fintype.card (Fin 5))=3/5 ∧
    (3/5 : ℝ)=0.6 := by
  classical
  have h : p2ViableActions={0,1,2} := by
    ext a
    fin_cases a <;> simp [p2ViableActions,p2Successor,p2Kernel]
  rw [h]
  norm_num [p2Successor]

def p5Next (s : Fin 5) (go : Bool) : Fin 5 :=
  if s=0 then if go then 1 else 0 else if s=1 then 2 else if s=3 then 3 else 4
def p5Safe : Set (Fin 5) := {s | s≠4}
def p5Kernel : Set (Fin 5) := {0,3}
def p5Round : ℕ→Set (Fin 5)
  | 0 => p5Safe
  | n+1 => viabilityStep p5Next allowed (p5Round n)

theorem actual_p5_every_printed_pruning_round_and_stopping :
    p5Round 0={0,1,2,3} ∧ p5Round 1={0,1,3} ∧ p5Round 2=p5Kernel ∧
    ∀n, p5Round (n+2)=p5Kernel := by
  have h0 : p5Round 0={0,1,2,3} := by ext s; fin_cases s <;> simp [p5Round,p5Safe,p5Next,p5Kernel,viabilityStep,controlledPre,allowed]
  have h1 : p5Round 1={0,1,3} := by ext s; fin_cases s <;> simp [p5Round,p5Safe,p5Next,p5Kernel,viabilityStep,controlledPre,allowed]
  have h2 : p5Round 2=p5Kernel := by ext s; fin_cases s <;> simp [p5Round,p5Safe,p5Next,p5Kernel,viabilityStep,controlledPre,allowed]
  have hk : viabilityStep p5Next allowed p5Kernel=p5Kernel := by ext s; fin_cases s <;> simp [p5Round,p5Safe,p5Next,p5Kernel,viabilityStep,controlledPre,allowed]
  refine ⟨h0,h1,h2,?_⟩
  intro n
  induction n with
  | zero => simpa using h2
  | succ n ih =>
    change viabilityStep p5Next allowed (p5Round (n+2))=p5Kernel
    rw [ih,hk]

theorem actual_p5_kernel_is_the_greatest_control_invariant_subset :
    IsGreatest {Y : Set (Fin 5) | Y⊆p5Safe ∧ Y⊆controlledPre p5Next allowed Y} p5Kernel := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro s hs
    rcases hs with h|h <;> subst s <;> simp [p5Safe]
  · intro s hs
    rcases hs with h|h <;> subst s <;> exact ⟨false,trivial,by simp [p5Next,p5Kernel]⟩
  · rintro Y ⟨hYs,hY⟩ s hs
    have h1 : Y⊆p5Round 1 := by
      intro x hx
      obtain ⟨a,ha,hnext⟩ := hY hx
      exact ⟨hYs hx,a,ha,hYs hnext⟩
    have h2 : Y⊆p5Round 2 := by
      intro x hx
      obtain ⟨a,ha,hnext⟩ := hY hx
      exact ⟨h1 hx,a,ha,h1 hnext⟩
    rw [actual_p5_every_printed_pruning_round_and_stopping.2.2.1] at h2
    exact h2 hs

theorem actual_p5_true_all_time_viability_iff (initial : Fin 5) :
    (∃x : ℕ→Fin 5, ∃a : ℕ→Bool,
      x 0=initial ∧ ∀n, x n∈p5Safe ∧ x (n+1)=p5Next (x n) (a n)) ↔ initial∈p5Kernel := by
  have h := actual_greatest_control_invariant_set_is_the_true_all_time_viability_kernel
    p5Next allowed p5Safe p5Kernel actual_p5_kernel_is_the_greatest_control_invariant_subset initial
  constructor
  · rintro ⟨x,a,h0,hpath⟩
    exact h.mpr ⟨x,a,h0,fun n=>⟨(hpath n).1,trivial,(hpath n).2⟩⟩
  · intro hi
    obtain ⟨x,a,h0,hpath⟩ := h.mp hi
    exact ⟨x,a,h0,fun n=>⟨(hpath n).1,(hpath n).2.2⟩⟩

theorem actual_p8_true_interval_maximum (z r : ℝ) (hr : 0≤r) :
    IsGreatest (abs '' Icc (z-r) (z+r)) (|z|+r) := by
  refine ⟨?_,?_⟩
  · by_cases hz : 0≤z
    · refine ⟨z+r,⟨by linarith,le_rfl⟩,?_⟩
      rw [abs_of_nonneg (by linarith),abs_of_nonneg hz]
    · have hn : z<0 := lt_of_not_ge hz
      refine ⟨z-r,⟨le_rfl,by linarith⟩,?_⟩
      rw [abs_of_nonpos (by linarith),abs_of_nonpos hn.le]
      ring
  · rintro y ⟨x,hx,rfl⟩
    apply abs_le.mpr
    have hz := abs_le.mp (le_refl |z|)
    constructor <;> linarith [hx.1,hx.2,hz.1,hz.2]

theorem actual_p8_every_successor_in_the_tube_is_safe_iff (z r : ℝ) (hr : 0≤r) :
    (∀x∈Icc (z-r) (z+r), |x|≤1) ↔ |z|+r≤1 := by
  have h := actual_p8_true_interval_maximum z r hr
  constructor
  · intro hall
    obtain ⟨x,hx,heq⟩ := h.1
    rw [←heq]
    exact hall x hx
  · intro hbound x hx
    exact (h.2 ⟨x,hx,rfl⟩).trans hbound

theorem actual_p8_two_source_tubes_and_unsafe_endpoint :
    |(7/10 : ℝ)|+1/5=9/10 ∧ |(9/10 : ℝ)|+1/5=11/10 ∧
    (∀x∈Icc (7/10-1/5 : ℝ) (7/10+1/5), |x|≤1) ∧
    (11/10 : ℝ)∈Icc (9/10-1/5) (9/10+1/5) ∧ ¬|(11/10 : ℝ)|≤1 := by
  refine ⟨by norm_num,by norm_num,?_,by norm_num,by norm_num⟩
  exact (actual_p8_every_successor_in_the_tube_is_safe_iff (7/10) (1/5) (by norm_num)).mpr (by norm_num)

end SafeLearning.CompleteAppliedViabilityFinitePractices20
