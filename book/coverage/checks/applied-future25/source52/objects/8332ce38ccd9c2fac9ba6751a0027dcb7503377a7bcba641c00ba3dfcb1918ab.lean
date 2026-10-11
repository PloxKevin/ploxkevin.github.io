import SafeLearning.CompleteMonitoringMeans22

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteModulesMonitoringBlocksClosed22

/-- Completed rounds1,...,n, including two actual transit states in each round. -/
def elapsed (n : ℕ) : ℕ := n*(n+3)

theorem actual_elapsed_successor (n : ℕ) : elapsed (n+1)=elapsed n+2*n+4 := by
  unfold elapsed
  ring

private theorem elapsed_mono : Monotone elapsed := by
  intro m n h
  exact Nat.mul_le_mul h (Nat.add_le_add_right h 3)

private theorem stage_exists (t : ℕ) : ∃ n, t<elapsed (n+1) := by
  refine ⟨t,?_⟩
  unfold elapsed
  nlinarith

def stageIndex (t : ℕ) : ℕ := Nat.find (stage_exists t)
def stageState (n r : ℕ) : Fin 3 :=
  if r=0 ∨ r=n+2 then 0 else if r≤n+1 then 1 else 2

def path (t : ℕ) : Fin 3 := stageState (stageIndex t) (t-elapsed (stageIndex t))
def visits (T : ℕ) (s : Fin 3) : ℕ := ∑ t ∈ Finset.range T, if path t=s then 1 else 0

theorem actual_stage_index_at_every_offset (n r : ℕ) (hr : r<2*n+4) :
    stageIndex (elapsed n+r)=n := by
  unfold stageIndex
  apply (Nat.find_eq_iff _).mpr
  constructor
  · rw [actual_elapsed_successor]
    omega
  · intro m hm
    have h : elapsed (m+1)≤elapsed n := elapsed_mono (by omega)
    omega

theorem actual_path_at_every_round_offset (n r : ℕ) (hr : r<2*n+4) :
    path (elapsed n+r)=stageState n r := by
  simp only [path,actual_stage_index_at_every_offset n r hr,Nat.add_sub_cancel_left]

theorem actual_round_has_the_two_transits_and_both_growing_blocks (n k : ℕ)
    (hk : k<n+1) :
    path (elapsed n)=0 ∧ path (elapsed n+n+2)=0 ∧
    path (elapsed n+(k+1))=1 ∧ path (elapsed n+(n+3+k))=2 := by
  have a:=actual_path_at_every_round_offset n 0 (by omega)
  have b:=actual_path_at_every_round_offset n (n+2) (by omega)
  have c:=actual_path_at_every_round_offset n (k+1) (by omega)
  have d:=actual_path_at_every_round_offset n (n+3+k) (by omega)
  simp only [Nat.add_zero] at a
  have hb : elapsed n+n+2=elapsed n+(n+2) := by omega
  rw [hb]
  rw [a,b,c,d]
  refine ⟨by simp [stageState],by simp [stageState],?_,?_⟩
  · simp [stageState,show k+1≠0 by omega,show k+1≠n+2 by omega,
      show k+1≤n+1 by omega] <;> omega
  · simp [stageState,show n+3+k≠0 by omega,show n+3+k≠n+2 by omega,
      show ¬n+3+k≤n+1 by omega]



theorem actual_every_horizon_has_the_actual_stage_bounds (T : ℕ) :
    elapsed (stageIndex T)≤T ∧ T<elapsed (stageIndex T+1) := by
  have hu : T<elapsed (stageIndex T+1) := Nat.find_spec (stage_exists T)
  refine ⟨?_,hu⟩
  by_cases hz : stageIndex T=0
  · simp [hz,elapsed]
  · have hp : stageIndex T-1<stageIndex T := by omega
    have hm:=Nat.find_min (stage_exists T) hp
    have he : stageIndex T-1+1=stageIndex T := by omega
    rw [he] at hm
    omega

private theorem stageState_first (n k : ℕ) (hk : k<n+1) : stageState n (k+1)=1 := by
  unfold stageState
  rw [if_neg (by omega),if_pos (by omega)]

private theorem stageState_second (n k : ℕ) (hk : k<n+1) : stageState n (n+3+k)=2 := by
  unfold stageState
  rw [if_neg (by omega),if_neg (by omega)]

theorem actual_one_round_indicator_sum (n : ℕ) (s : Fin 3) :
    (∑ r ∈ Finset.range (2*n+4), if stageState n r=s then 1 else 0) =
      (if s=0 then 2 else n+1) := by
  have hsize : 2*n+4=(n+2)+(n+2) := by omega
  rw [hsize,Finset.sum_range_add]
  have hfirst : (∑ r ∈ Finset.range (n+2), if stageState n r=s then 1 else 0) =
      (if (0:Fin 3)=s then 1 else 0)+(n+1)*(if (1:Fin 3)=s then 1 else 0) := by
    rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ']
    have hz : stageState n 0=0 := by simp [stageState]
    rw [hz]
    have he : ∀ k ∈ Finset.range (n+1),
        (if stageState n (k+1)=s then 1 else 0) = (if (1:Fin 3)=s then 1 else 0) := by
      intro k hk
      rw [stageState_first n k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl he]
    simp [Nat.add_comm]
  have hsecond : (∑ r ∈ Finset.range (n+2), if stageState n (n+2+r)=s then 1 else 0) =
      (if (0:Fin 3)=s then 1 else 0)+(n+1)*(if (2:Fin 3)=s then 1 else 0) := by
    rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ']
    have hz : stageState n (n+2+0)=0 := by simp [stageState]
    rw [hz]
    have he : ∀ k ∈ Finset.range (n+1),
        (if stageState n (n+2+(k+1))=s then 1 else 0) = (if (2:Fin 3)=s then 1 else 0) := by
      intro k hk
      rw [show n+2+(k+1)=n+3+k by omega,stageState_second n k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl he]
    simp [Nat.add_comm]
  rw [hfirst,hsecond]
  fin_cases s <;> simp <;> omega


theorem actual_completed_round_visit_counts (n : ℕ) :
    visits (elapsed n) 0=2*n ∧
    2*visits (elapsed n) 1=n*(n+1) ∧
    2*visits (elapsed n) 2=n*(n+1) := by
  induction n with
  | zero => simp [visits,elapsed]
  | succ n ih =>
    have hstep (s : Fin 3) : visits (elapsed (n+1)) s =
        visits (elapsed n) s+(if s=0 then 2 else n+1) := by
      unfold visits
      rw [show elapsed (n+1)=elapsed n+(2*n+4) by rw [actual_elapsed_successor];omega,
        Finset.sum_range_add]
      congr 1
      have he : ∀ r ∈ Finset.range (2*n+4),
          (if path (elapsed n+r)=s then 1 else 0)=
          (if stageState n r=s then 1 else 0) := by
        intro r hr
        rw [actual_path_at_every_round_offset n r (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl he,actual_one_round_indicator_sum]
    obtain ⟨h0,h1,h2⟩:=ih
    constructor
    · rw [hstep];simp;omega
    constructor
    · rw [hstep];simp;nlinarith
    · rw [hstep];simp;nlinarith

theorem actual_visit_counts_are_monotone (s : Fin 3) : Monotone (fun T => visits T s) := by
  intro m n h
  unfold visits
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i hi hn
  positivity

theorem actual_all_horizon_count_enclosures (T : ℕ) :
    let n:=stageIndex T
    2*n ≤ visits T 0 ∧ visits T 0 ≤ 2*(n+1) ∧
    n*(n+1) ≤ 2*visits T 1 ∧ 2*visits T 1 ≤ (n+1)*(n+2) ∧
    n*(n+1) ≤ 2*visits T 2 ∧ 2*visits T 2 ≤ (n+1)*(n+2) := by
  dsimp only
  obtain ⟨hl,hu⟩:=actual_every_horizon_has_the_actual_stage_bounds T
  have lo (s : Fin 3): visits (elapsed (stageIndex T)) s≤visits T s :=
    actual_visit_counts_are_monotone s hl
  have up (s : Fin 3): visits T s≤visits (elapsed (stageIndex T+1)) s :=
    actual_visit_counts_are_monotone s (by omega)
  obtain ⟨h0,h1,h2⟩:=actual_completed_round_visit_counts (stageIndex T)
  obtain ⟨j0,j1,j2⟩:=actual_completed_round_visit_counts (stageIndex T+1)
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [lo 0,lo 1,lo 2,up 0,up 1,up 2]

end SafeLearning.CompleteModulesMonitoringBlocksClosed22
