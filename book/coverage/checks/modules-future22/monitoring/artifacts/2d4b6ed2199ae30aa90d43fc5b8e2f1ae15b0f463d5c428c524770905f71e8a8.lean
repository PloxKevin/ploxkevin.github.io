import SafeLearning.CompleteMonitoringMeans22

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteModulesMonitoringBlocks22

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
  simp only [stageState]
  split_ifs <;> omega

end SafeLearning.CompleteModulesMonitoringBlocks22
