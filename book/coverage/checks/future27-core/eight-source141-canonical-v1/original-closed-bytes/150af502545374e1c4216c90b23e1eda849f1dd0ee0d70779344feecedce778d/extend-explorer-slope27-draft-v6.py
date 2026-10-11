from pathlib import Path
import hashlib,json,re
p=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v5.lean');s=p.read_text()
s=s.replace('open Set\n','open Set MeasureTheory\n',1)
needle='def discountedReward'
new='''theorem actual_unviable_state_action_reward_supremum_is_zero
    (cost goalReward : ℝ) (hc : 0 ≤ cost) :
    sSup (Set.range (fun q : unviableStates × Action => reward cost goalReward q.1.val)) = 0 := by
  have he : Set.range (fun q : unviableStates × Action => reward cost goalReward q.1.val) =
      reward cost goalReward '' unviableStates := by
    ext v
    constructor
    · rintro ⟨⟨⟨state, hs⟩, action⟩, rfl⟩
      exact ⟨state, hs, rfl⟩
    · rintro ⟨state, hs, rfl⟩
      exact ⟨(⟨state, hs⟩, .down), rfl⟩
  rw [he]
  exact actual_unviable_reward_supremum_is_zero cost goalReward hc

theorem actual_every_unviable_grid_path_fails_by_two
    (states : ℕ → State) (actions : ℕ → Action)
    (hzero : states 0 ∈ unviableStates)
    (hlegal : ∀ n, available (states n) (actions n))
    (hstep : ∀ n, states (n + 1) = step (states n) (actions n)) :
    ∃ failure ≤ 2, states failure = .failure ∧
      ∀ n, failure < n → states n = .sink := by
  by_cases h0 : states 0 = .failure
  · refine ⟨0, by omega, h0, ?_⟩
    have hsink : states 1 = .sink := by simpa [h0, step] using hstep 0
    intro n hn
    exact actual_sink_tail states actions 1 hsink hstep n (by omega)
  · have hearly : states 1 = .failure ∨ states 2 = .failure := by
      have h1 := hstep 0
      have h2 := hstep 1
      have ha := hlegal 0
      have hb := hlegal 1
      cases hs : states 0 with
      | failure => exact False.elim (h0 hs)
      | sink => simp [hs, unviableStates, world] at hzero
      | live row col =>
        cases ha0 : actions 0 <;> cases ha1 : actions 1 <;>
          fin_cases row <;> fin_cases col <;>
          simp_all [unviableStates, world, kernelStates, available,
            step, cell, slope, movedRow, movedCol]
    rcases hearly with h1 | h2
    · refine ⟨1, by omega, h1, ?_⟩
      have hsink : states 2 = .sink := by simpa [h1, step] using hstep 1
      intro n hn
      exact actual_sink_tail states actions 2 hsink hstep n (by omega)
    · refine ⟨2, by omega, h2, ?_⟩
      have hsink : states 3 = .sink := by simpa [h2, step] using hstep 2
      intro n hn
      exact actual_sink_tail states actions 3 hsink hstep n (by omega)

'''
# This theorem uses actual_sink_tail, so it must go AFTER that declaration.
start=new.index('theorem actual_every_unviable_grid_path_fails_by_two')
rewardnew=new[:start];failure_new=new[start:]
s=s.replace(needle,rewardnew+needle)
s=s.replace('theorem actual_every_upper_path_has_the_two_failure_patterns',failure_new+'theorem actual_every_upper_path_has_the_two_failure_patterns')
needle='theorem single_failure_discounted_risk_is_arrival_weight'
new='''/-- Finite support derives integrability, rather than making it an assumption. -/
theorem actual_finite_support_counting_integral_is_its_sum
    (terms : ℕ → ℝ) (length : ℕ) (hz : ∀ n, length ≤ n → terms n = 0) :
    Integrable terms Measure.count ∧
      (∫ n : ℕ, terms n ∂Measure.count) = ∑ n ∈ Finset.range length, terms n := by
  have hvanish (n : ℕ) (hn : n ∉ Finset.range length) : terms n = 0 := by
    apply hz n
    simpa only [Finset.mem_range, not_lt] using hn
  have hnorm : Summable (fun n => ‖terms n‖) :=
    summable_of_ne_finset_zero (s := Finset.range length) (by
      intro n hn
      simp [hvanish n hn])
  have hi : Integrable terms Measure.count := integrable_count_iff.mpr hnorm
  refine ⟨hi, ?_⟩
  rw [integral_countable hi]
  simp only [measureReal_def, Measure.count_apply_singleton,
    ENNReal.toReal_one, one_smul]
  exact tsum_eq_sum hvanish

theorem actual_stopped_counting_integral_is_the_printed_finite_reward_sum
    (discount : ℝ) (rewards : ℕ → ℝ) (failure : ℕ)
    (hz : ∀ n, failure < n → rewards n = 0) :
    Integrable (fun n => discount ^ n * rewards n) Measure.count ∧
      (∫ n : ℕ, discount ^ n * rewards n ∂Measure.count) =
        ∑ n ∈ Finset.range (failure + 1), discount ^ n * rewards n := by
  apply actual_finite_support_counting_integral_is_its_sum
  intro n hn
  simp [hz n (by omega)]

'''
s=s.replace(needle,new+needle)
needle='theorem nonnegative_reward_bound_allows_horizon_extension'
new='''theorem actual_single_failure_counting_integral_is_arrival_weight
    (discount : ℝ) (failure : ℕ) :
    Integrable (fun n : ℕ => discount ^ n * (if n = failure then 1 else 0 : ℝ)) Measure.count ∧
      (∫ n : ℕ, discount ^ n * (if n = failure then 1 else 0 : ℝ) ∂Measure.count) =
        discount ^ failure := by
  have hvanish : ∀ n : ℕ, failure + 1 ≤ n →
      discount ^ n * (if n = failure then 1 else 0 : ℝ) = 0 := by
    intro n hn
    simp [show n ≠ failure by omega]
  have hi := actual_finite_support_counting_integral_is_its_sum
    (fun n : ℕ => discount ^ n * (if n = failure then 1 else 0 : ℝ)) (failure + 1) hvanish
  refine ⟨hi.1, ?_⟩
  rw [integral_countable hi.1]
  simp only [measureReal_def, Measure.count_apply_singleton,
    ENNReal.toReal_one, one_smul]
  exact single_failure_discounted_risk_is_arrival_weight _ _

'''
s=s.replace(needle,new+needle)
needle='end SafeLearning.CompleteAppliedExplorerSlope27'
new='''/-- This is the source supremum convention even when the unviable set is empty.
For a nonempty set it coincides with the real-valued outer supremum above. -/
theorem source_extended_outer_supremum_preserves_the_uniform_doomed_bound
    {X Controller : Type*} [Nonempty Controller]
    (discount bound penalty : ℝ) (rewards : X → Controller → ℕ → ℝ)
    (failure : X → Controller → ℕ) (horizon : ℕ)
    (hd : 0 ≤ discount) (hd1 : discount < 1) (hb : 0 ≤ bound) (hp : 0 ≤ penalty)
    (ht : ∀ x u, failure x u ≤ horizon)
    (hr : ∀ x u n, n < failure x u + 1 → rewards x u n ≤ bound)
    (hz : ∀ x u n, failure x u < n → rewards x u n = 0) :
    sSup (Set.range (fun x => ((sSup (Set.range (fun u =>
      (∑' n, discount ^ n * rewards x u n) - penalty *
        (∑' n : ℕ, discount ^ n * (if n = failure x u then 1 else 0 : ℝ))))) : ℝ) : EReal))) ≤
      ((bound * (1 - discount ^ (horizon + 1)) / (1 - discount) -
        penalty * discount ^ horizon : ℝ) : EReal) := by
  apply sSup_le
  rintro _ ⟨x, rfl⟩
  apply EReal.coe_le_coe
  apply CompleteModulesValues.supremum_doomed_bound
  · exact Set.range_nonempty _
  · intro u
    exact counting_sum_doomed_return_bound _ _ _ _ _ _ hd hd1 hb hp (ht x u)
      (hr x u) (hz x u)

'''
s=s.replace(needle,new+needle)
q=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v6.lean');assert not q.exists();q.write_text(s)
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
print(json.dumps({'file':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'lines':len(s.splitlines()),'theorem_count':len(re.findall(r'^theorem ',s,re.M)),'status':'uncompiled TMP draft v6; earlier drafts preserved'}))
