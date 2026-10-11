from pathlib import Path
import hashlib,json,re
p=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v6.lean');s=p.read_text()
needle='theorem actual_every_upper_path_has_the_two_failure_patterns'
new='''/-- The literal transition to the sink makes the failure event one-time. -/
theorem actual_grid_failure_is_visited_at_exactly_one_time
    (states : ℕ → State) (actions : ℕ → Action) (failure : ℕ)
    (hstep : ∀ n, states (n + 1) = step (states n) (actions n))
    (hhit : states failure = .failure) :
    ∀ n, states n = .failure ↔ n = failure := by
  have hsink : states (failure + 1) = .sink := by
    rw [hstep, hhit]
    rfl
  have htail := actual_sink_tail states actions (failure + 1) hsink hstep
  intro n
  constructor
  · intro hnfail
    by_contra hn
    by_cases hlt : n < failure
    · have hnsink : states (n + 1) = .sink := by rw [hstep, hnfail]; rfl
      have htf := actual_sink_tail states actions (n + 1) hnsink hstep failure (by omega)
      rw [hhit] at htf
      contradiction
    · have hnsink := htail n (by omega)
      rw [hnfail] at hnsink
      contradiction
  · rintro rfl
    exact hhit

'''
s=s.replace(needle,new+needle)
needle='theorem nonnegative_reward_bound_allows_horizon_extension'
new='''/-- No one-time-charge or vanishing-tail assumption is needed for this actual grid path. -/
theorem actual_grid_arrival_derives_the_counting_reward_and_risk
    (discount cost goalReward : ℝ) (states : ℕ → State) (actions : ℕ → Action)
    (failure : ℕ) (hstep : ∀ n, states (n + 1) = step (states n) (actions n))
    (hhit : states failure = .failure) :
    discountedReward discount cost goalReward states =
      ∑ n ∈ Finset.range (failure + 1), discount ^ n * reward cost goalReward (states n) ∧
    discountedRisk discount states = discount ^ failure := by
  have hsink : states (failure + 1) = .sink := by rw [hstep, hhit]; rfl
  have htail := actual_sink_tail states actions (failure + 1) hsink hstep
  have honce := actual_grid_failure_is_visited_at_exactly_one_time states actions failure hstep hhit
  constructor
  · apply stopped_discounted_reward_is_finite_prefix
    intro n hn
    simp [htail n (by omega), reward]
  · unfold discountedRisk
    have hcharge (n : ℕ) : failureCharge (states n) = (if n = failure then 1 else 0 : ℝ) := by
      by_cases hn : n = failure
      · subst n
        simp [hhit, failureCharge]
      · have hnf : states n ≠ .failure := fun h => hn ((honce n).mp h)
        cases he : states n <;> simp_all [failureCharge]
    simp_rw [hcharge]
    exact single_failure_discounted_risk_is_arrival_weight discount failure

'''
s=s.replace(needle,new+needle)
q=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v7.lean');assert not q.exists();q.write_text(s)
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
print(json.dumps({'file':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'lines':len(s.splitlines()),'theorem_count':len(re.findall(r'^theorem ',s,re.M)),'status':'uncompiled TMP draft v7; all earlier drafts unchanged'}))
