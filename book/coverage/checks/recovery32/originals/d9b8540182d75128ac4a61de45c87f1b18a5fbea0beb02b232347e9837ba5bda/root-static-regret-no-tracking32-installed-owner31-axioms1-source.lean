import Mathlib

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32

/-- The two printed reward rounds are repeated forever; the learner always plays A. -/
def rewardA (t : ℕ) : ℝ := if t % 2 = 0 then 1 else 0
def rewardB (t : ℕ) : ℝ := 1 - rewardA t
def totalA (N : ℕ) : ℝ := ∑ t ∈ Finset.range N, rewardA t
def totalB (N : ℕ) : ℝ := ∑ t ∈ Finset.range N, rewardB t
def staticRegret (N : ℕ) : ℝ := max (totalA N) (totalB N) - totalA N
def dynamicRegret (N : ℕ) : ℝ := (∑ t ∈ Finset.range N, max (rewardA t) (rewardB t)) - totalA N
def trackingGap (t : ℕ) : ℝ := max (rewardA t) (rewardB t) - rewardA t

theorem rewardA_even (n : ℕ) : rewardA (2 * n) = 1 := by simp [rewardA]
theorem rewardA_odd (n : ℕ) : rewardA (2 * n + 1) = 0 := by simp [rewardA, Nat.add_mod]
theorem rewardB_even (n : ℕ) : rewardB (2 * n) = 0 := by simp [rewardB, rewardA_even]
theorem rewardB_odd (n : ℕ) : rewardB (2 * n + 1) = 1 := by simp [rewardB, rewardA_odd]

theorem actual_reward_bounds (t : ℕ) : rewardA t ∈ Set.Icc (0 : ℝ) 1 ∧ rewardB t ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : t % 2 = 0 <;> simp [rewardA, rewardB, h]

theorem totalA_succ (N : ℕ) : totalA (N + 1) = totalA N + rewardA N := by
  simp [totalA, Finset.sum_range_succ]

theorem actual_totalA_even (n : ℕ) : totalA (2 * n) = (n : ℝ) := by
  induction n with
  | zero => simp [totalA]
  | succ n ih =>
    have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hn, totalA_succ, totalA_succ, ih, rewardA_even, rewardA_odd]
    push_cast
    ring

theorem actual_totalA_odd (n : ℕ) : totalA (2 * n + 1) = (n : ℝ) + 1 := by
  rw [totalA_succ, actual_totalA_even, rewardA_even]

theorem actual_totalB_complement (N : ℕ) : totalB N = (N : ℝ) - totalA N := by
  simp [totalB, totalA, rewardB, Finset.sum_sub_distrib]

theorem actual_totalB_even (n : ℕ) : totalB (2 * n) = (n : ℝ) := by
  rw [actual_totalB_complement, actual_totalA_even]
  push_cast
  ring

theorem actual_totalB_odd (n : ℕ) : totalB (2 * n + 1) = (n : ℝ) := by
  rw [actual_totalB_complement, actual_totalA_odd]
  push_cast
  ring

theorem actual_A_is_best_fixed_for_every_horizon (N : ℕ) : totalB N ≤ totalA N := by
  have hd : N = 2 * (N / 2) + N % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · rw [h, add_zero] at hd
    rw [hd, actual_totalA_even, actual_totalB_even]
  · rw [h] at hd
    rw [hd, actual_totalA_odd, actual_totalB_odd]
    linarith

theorem actual_static_regret_zero_for_every_horizon (N : ℕ) : staticRegret N = 0 := by
  simp [staticRegret, max_eq_left (actual_A_is_best_fixed_for_every_horizon N)]

theorem actual_vanishing_average_static_regret :
    Tendsto (fun N : ℕ => staticRegret N / (N : ℝ)) atTop (𝓝 0) := by
  simpa [actual_static_regret_zero_for_every_horizon] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem actual_changing_best_reward (t : ℕ) : max (rewardA t) (rewardB t) = 1 := by
  by_cases h : t % 2 = 0 <;> simp [rewardA, rewardB, h]

theorem actual_dynamic_regret (N : ℕ) : dynamicRegret N = (N : ℝ) - totalA N := by
  simp [dynamicRegret, actual_changing_best_reward]

theorem actual_positive_even_average_dynamic_regret (n : ℕ) (hn : 0 < n) :
    dynamicRegret (2 * n) / (2 * n : ℕ) = (1 / 2 : ℝ) := by
  rw [actual_dynamic_regret, actual_totalA_even]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
  ring

theorem actual_odd_round_tracking_gap (n : ℕ) : trackingGap (2 * n + 1) = 1 := by
  rw [trackingGap, actual_changing_best_reward, rewardA_odd]
  norm_num

theorem actual_tracking_gap_does_not_vanish :
    ¬ Tendsto trackingGap atTop (𝓝 (0 : ℝ)) := by
  intro h
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, actual_odd_round_tracking_gap] using h.comp hodd
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  norm_num at hbad

theorem actual_printed_two_round_case : staticRegret 2 = 0 ∧ dynamicRegret 2 = 1 := by
  constructor
  · exact actual_static_regret_zero_for_every_horizon 2
  · change dynamicRegret (2 * 1) = 1
    rw [actual_dynamic_regret, actual_totalA_even]
    norm_num

end SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32

#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.rewardA_even
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.rewardA_odd
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.rewardB_even
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.rewardB_odd
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_reward_bounds
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.totalA_succ
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_totalA_even
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_totalA_odd
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_totalB_complement
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_totalB_even
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_totalB_odd
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_A_is_best_fixed_for_every_horizon
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_static_regret_zero_for_every_horizon
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_vanishing_average_static_regret
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_changing_best_reward
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_dynamic_regret
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_positive_even_average_dynamic_regret
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_odd_round_tracking_gap
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_tracking_gap_does_not_vanish
#print axioms SafeLearning.CompleteAppliedStaticRegretDoesNotTrack32.actual_printed_two_round_case
