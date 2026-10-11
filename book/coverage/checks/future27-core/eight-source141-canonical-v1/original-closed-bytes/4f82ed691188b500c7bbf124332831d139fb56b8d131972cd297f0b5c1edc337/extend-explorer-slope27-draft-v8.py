from pathlib import Path
import hashlib,json
old=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v7.lean')
new=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v8.lean')
assert not new.exists()
addition=r'''

namespace SafeLearning.CompleteAppliedExplorerSlope27

/-- The source reward supremum is over physical unviable states, not the
post-failure bookkeeping sink. Boundedness comes from the source reward scope. -/
theorem actual_reward_supremum_bounds_each_physical_unviable_state_action
    {S A : Type*} (physical kernel : Set S) (r : S → A → ℝ)
    (hbounded : BddAbove (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)))
    (x : S) (hx : x ∈ physical) (hxk : x ∉ kernel) (a : A) :
    r x a ≤ sSup (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)) := by
  exact le_csSup hbounded ⟨(⟨x, ⟨hx, hxk⟩⟩, a), rfl⟩

/-- Every visited reward bound is derived from the actual physical-state
supremum and the greatest-kernel property; no bound outside the world is
required. The explicit arrival and sink semantics match the source. -/
theorem source_physical_unviable_trajectory_counting_sum_bound
    {S A : Type*} (dynamics : S → A → S) (allowed : S → A → Prop)
    (physical safe kernel failureStates : Set S)
    (hk : IsGreatest {Y : Set S | Y ⊆ safe ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre dynamics allowed Y} kernel)
    (states : ℕ → S) (actions : ℕ → A) (r : S → A → ℝ)
    (discount bound penalty : ℝ) (failure horizon : ℕ)
    (hd : 0 ≤ discount) (hd1 : discount < 1) (hb : 0 ≤ bound) (hp : 0 ≤ penalty)
    (ht : failure ≤ horizon) (hzero : states 0 ∉ kernel)
    (hphysical : ∀ n ≤ failure, states n ∈ physical)
    (hsafe : ∀ n < failure, states n ∈ safe)
    (hallowed : ∀ n, allowed (states n) (actions n))
    (hstep : ∀ n, states (n + 1) = dynamics (states n) (actions n))
    (hbounded : BddAbove (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)))
    (hsup : sSup (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)) ≤ bound)
    (hz : ∀ n, failure < n → r (states n) (actions n) = 0)
    (hfailure : ∀ n, states n ∈ failureStates ↔ n = failure) :
    (∑' n, discount ^ n * r (states n) (actions n)) -
      penalty * (∑' n : ℕ, discount ^ n * (if states n ∈ failureStates then 1 else 0 : ℝ)) ≤
      bound * (1 - discount ^ (horizon + 1)) / (1 - discount) - penalty * discount ^ horizon := by
  have hvisited := actual_every_visited_prefailure_state_is_unviable dynamics allowed safe kernel hk
    states actions failure hzero hsafe hallowed hstep
  simp_rw [hfailure]
  apply counting_sum_doomed_return_bound _ _ _ _ _ _ hd hd1 hb hp ht
  · intro n hn
    exact le_trans (actual_reward_supremum_bounds_each_physical_unviable_state_action
      physical kernel r hbounded (states n) (hphysical n (by omega))
      (hvisited n (by omega)) (actions n)) hsup
  · exact hz

/-- The source's two suprema now range over actual state/control trajectories.
An empty unviable initial-state domain has extended supremum minus infinity. -/
theorem source_actual_state_and_controller_suprema_have_the_uniform_bound
    {S A X Controller : Type*} [Nonempty Controller]
    (dynamics : S → A → S) (allowed : S → A → Prop)
    (physical safe kernel failureStates : Set S)
    (hk : IsGreatest {Y : Set S | Y ⊆ safe ∧
      Y ⊆ CompleteFoundationsGraphViability.controlledPre dynamics allowed Y} kernel)
    (states : X → Controller → ℕ → S) (actions : X → Controller → ℕ → A)
    (r : S → A → ℝ) (failure : X → Controller → ℕ)
    (discount bound penalty : ℝ) (horizon : ℕ)
    (hd : 0 ≤ discount) (hd1 : discount < 1) (hb : 0 ≤ bound) (hp : 0 ≤ penalty)
    (ht : ∀ x u, failure x u ≤ horizon)
    (hzero : ∀ x u, states x u 0 ∉ kernel)
    (hphysical : ∀ x u n, n ≤ failure x u → states x u n ∈ physical)
    (hsafe : ∀ x u n, n < failure x u → states x u n ∈ safe)
    (hallowed : ∀ x u n, allowed (states x u n) (actions x u n))
    (hstep : ∀ x u n, states x u (n + 1) = dynamics (states x u n) (actions x u n))
    (hbounded : BddAbove (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)))
    (hsup : sSup (Set.range (fun q : (physical \ kernel) × A => r q.1.val q.2)) ≤ bound)
    (hz : ∀ x u n, failure x u < n → r (states x u n) (actions x u n) = 0)
    (hfailure : ∀ x u n, states x u n ∈ failureStates ↔ n = failure x u) :
    sSup (Set.range (fun x => ((sSup (Set.range (fun u =>
      (∑' n, discount ^ n * r (states x u n) (actions x u n)) - penalty *
        (∑' n : ℕ, discount ^ n * (if states x u n ∈ failureStates then 1 else 0 : ℝ))))) : ℝ) : EReal))) ≤
      ((bound * (1 - discount ^ (horizon + 1)) / (1 - discount) -
        penalty * discount ^ horizon : ℝ) : EReal) := by
  apply sSup_le
  rintro _ ⟨x, rfl⟩
  apply EReal.coe_le_coe
  apply CompleteModulesValues.supremum_doomed_bound
  · exact Set.range_nonempty _
  · intro u
    exact source_physical_unviable_trajectory_counting_sum_bound
      dynamics allowed physical safe kernel failureStates hk (states x u) (actions x u) r
      discount bound penalty (failure x u) horizon hd hd1 hb hp (ht x u) (hzero x u)
      (hphysical x u) (hsafe x u) (hallowed x u) (hstep x u) hbounded hsup
      (hz x u) (hfailure x u)

end SafeLearning.CompleteAppliedExplorerSlope27
'''
new.write_bytes(old.read_bytes()+addition.encode())
assert new.read_bytes().startswith(old.read_bytes())
print(json.dumps({'file':str(new),'sha256':hashlib.sha256(new.read_bytes()).hexdigest(),'prior_byte_prefix_exact':True,'new_theorem_bodies':3,'compiled':False}))
