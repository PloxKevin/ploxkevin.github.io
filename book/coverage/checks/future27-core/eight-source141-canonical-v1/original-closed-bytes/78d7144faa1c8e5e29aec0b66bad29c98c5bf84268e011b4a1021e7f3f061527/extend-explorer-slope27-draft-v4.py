from pathlib import Path
import hashlib,json,re
p=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v3.lean');s=p.read_text()
s=s.replace('import SafeLearning.CompleteModulesValues\n','import SafeLearning.CompleteModulesValues\nimport SafeLearning.CompleteFoundationsGraphViability\n')
needle='def discountedReward'
new='''/-- The post-failure sink is bookkeeping, excluded from the physical world. -/
def world : Set State := {s | s ≠ .sink}

def safeStates : Set State := {s | match s with
  | .live _ _ => True
  | _ => False}

def kernelStates : Set State := {s | match s with
  | .live row col => slope row.val col.val = false
  | _ => False}

def unviableStates : Set State := world \\ kernelStates

theorem actual_nonslope_stay_is_safe_self_loop (row : Fin 4) (col : Fin 8)
    (hs : slope row.val col.val = false) :
    step (.live row col) .stay = .live row col := by
  have hr : row.val ≤ 3 := by omega
  have hc : col.val ≤ 7 := by omega
  have hr4 : row.val ≠ 4 := by omega
  simp [step, hs, movedRow, movedCol, cell, hr4,
    Nat.min_eq_right hr, Nat.min_eq_right hc]

theorem actual_grid_kernel_is_greatest_control_invariant :
    IsGreatest {Y : Set State | Y ⊆ safeStates ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre step available Y} kernelStates := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s hs
    cases s <;> simp_all [safeStates, kernelStates]
  · intro s hs
    cases s with
    | live row col =>
      exact ⟨.stay, by simp [available], by
        rw [actual_nonslope_stay_is_safe_self_loop row col hs]
        exact hs⟩
    | failure => simp [kernelStates] at hs
    | sink => simp [kernelStates] at hs
  · rintro Y ⟨hYs, hY⟩ s hs
    cases s with
    | live row col =>
      change slope row.val col.val = false
      by_contra hnonslope
      obtain ⟨a, ha, hnext⟩ := hY hs
      obtain ⟨b, hb, hnext2⟩ := hY hnext
      have hsafe1 := hYs hnext
      have hsafe2 := hYs hnext2
      fin_cases row <;> fin_cases col <;> cases a <;> cases b <;>
        simp_all [safeStates, kernelStates, available, step, cell,
          slope, movedRow, movedCol]
    | failure => simpa [safeStates] using hYs hs
    | sink => simpa [safeStates] using hYs hs

theorem actual_grid_kernel_is_exact_all_time_viability (initial : State) :
    initial ∈ kernelStates ↔ ∃ states : ℕ → State, ∃ actions : ℕ → Action,
      states 0 = initial ∧ ∀ n, states n ∈ safeStates ∧
        available (states n) (actions n) ∧ states (n + 1) = step (states n) (actions n) := by
  exact CompleteFoundationsGraphViability.actual_greatest_control_invariant_set_is_the_true_all_time_viability_kernel
    step available safeStates kernelStates actual_grid_kernel_is_greatest_control_invariant initial

theorem actual_unviable_reward_is_nonpositive (cost goalReward : ℝ) (hc : 0 ≤ cost)
    (s : State) (hs : s ∈ unviableStates) : reward cost goalReward s ≤ 0 := by
  cases s with
  | live row col =>
    by_cases hg : row.val = 3 ∧ col.val = 7
    · have hk : State.live row col ∈ kernelStates := by
        simp [kernelStates, slope, hg.1, hg.2]
      exact False.elim (hs.2 hk)
    · simp [reward, hg]
      linarith
  | failure => simp [reward]
  | sink => simp [reward]

theorem actual_unviable_reward_supremum_is_zero (cost goalReward : ℝ) (hc : 0 ≤ cost) :
    sSup (reward cost goalReward '' unviableStates) = 0 := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨.failure, by simp [unviableStates, world, kernelStates], by simp [reward]⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact actual_unviable_reward_is_nonpositive _ _ hc s hs

'''
s=s.replace(needle,new+needle)
needle='theorem both_controller_and_state_suprema_preserve_counting_sum_bound'
new='''/-- Adding a safe predecessor of the greatest invariant set cannot enlarge it. -/
theorem actual_unviability_is_forward_invariant_before_failure
    {S A : Type*} (dynamics : S → A → S) (allowed : S → A → Prop)
    (safe kernel : Set S)
    (hk : IsGreatest {Y : Set S | Y ⊆ safe ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre dynamics allowed Y} kernel)
    (x : S) (a : A) (hx : x ∉ kernel) (hsafe : x ∈ safe) (ha : allowed x a) :
    dynamics x a ∉ kernel := by
  intro hnext
  have hgrown : insert x kernel ⊆ safe ∧ insert x kernel ⊆
      CompleteFoundationsGraphViability.controlledPre dynamics allowed (insert x kernel) := by
    constructor
    · intro y hy
      rcases hy with rfl | hy
      · exact hsafe
      · exact hk.1.1 hy
    · intro y hy
      rcases hy with rfl | hy
      · exact ⟨a, ha, Or.inr hnext⟩
      · obtain ⟨b, hb, hsuccessor⟩ := hk.1.2 hy
        exact ⟨b, hb, Or.inr hsuccessor⟩
  exact hx (hk.2 hgrown (by simp))

theorem actual_every_visited_prefailure_state_is_unviable
    {S A : Type*} (dynamics : S → A → S) (allowed : S → A → Prop)
    (safe kernel : Set S)
    (hk : IsGreatest {Y : Set S | Y ⊆ safe ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre dynamics allowed Y} kernel)
    (states : ℕ → S) (actions : ℕ → A) (failure : ℕ)
    (hzero : states 0 ∉ kernel) (hsafe : ∀ n < failure, states n ∈ safe)
    (hallowed : ∀ n, allowed (states n) (actions n))
    (hstep : ∀ n, states (n + 1) = dynamics (states n) (actions n)) :
    ∀ n ≤ failure, states n ∉ kernel := by
  intro n
  induction n with
  | zero => intro _; exact hzero
  | succ n ih =>
    intro hn
    rw [hstep n]
    exact actual_unviability_is_forward_invariant_before_failure dynamics allowed safe kernel hk
      _ _ (ih (by omega)) (hsafe n (by omega)) (hallowed n)

/-- The source's bound on X_U×U now supplies the actual visited reward bound. -/
theorem actual_unviable_trajectory_counting_sum_bound
    {S A : Type*} (dynamics : S → A → S) (allowed : S → A → Prop)
    (safe kernel failureStates : Set S)
    (hk : IsGreatest {Y : Set S | Y ⊆ safe ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre dynamics allowed Y} kernel)
    (states : ℕ → S) (actions : ℕ → A) (r : S → A → ℝ)
    (discount bound penalty : ℝ) (failure horizon : ℕ)
    (hd : 0 ≤ discount) (hd1 : discount < 1) (hb : 0 ≤ bound) (hp : 0 ≤ penalty)
    (ht : failure ≤ horizon) (hzero : states 0 ∉ kernel)
    (hsafe : ∀ n < failure, states n ∈ safe)
    (hallowed : ∀ n, allowed (states n) (actions n))
    (hstep : ∀ n, states (n + 1) = dynamics (states n) (actions n))
    (hr : ∀ x ∉ kernel, ∀ a, allowed x a → r x a ≤ bound)
    (hz : ∀ n, failure < n → r (states n) (actions n) = 0)
    (hfailure : ∀ n, states n ∈ failureStates ↔ n = failure) :
    (∑' n, discount ^ n * r (states n) (actions n)) -
      penalty * (∑' n : ℕ, discount ^ n * (if states n ∈ failureStates then 1 else 0 : ℝ)) ≤
      bound * (1 - discount ^ (horizon + 1)) / (1 - discount) - penalty * discount ^ horizon := by
  have hvisited := actual_every_visited_prefailure_state_is_unviable dynamics allowed safe kernel hk
    states actions failure hzero hsafe hallowed hstep
  have hevent : (fun n : ℕ => if states n ∈ failureStates then (1 : ℝ) else 0) =
      (fun n : ℕ => if n = failure then (1 : ℝ) else 0) := by
    funext n
    simp only [hfailure n]
  rw [hevent]
  apply counting_sum_doomed_return_bound _ _ _ _ _ _ hd hd1 hb hp ht
  · intro n hn
    exact hr (states n) (hvisited n (by omega)) (actions n) (hallowed n)
  · exact hz

'''
s=s.replace(needle,new+needle)
q=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v4.lean');assert not q.exists();q.write_text(s)
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
print(json.dumps({'file':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'lines':len(s.splitlines()),'theorem_count':len(re.findall(r'^theorem ',s,re.M)),'status':'uncompiled TMP draft v4; earlier drafts preserved'}))
