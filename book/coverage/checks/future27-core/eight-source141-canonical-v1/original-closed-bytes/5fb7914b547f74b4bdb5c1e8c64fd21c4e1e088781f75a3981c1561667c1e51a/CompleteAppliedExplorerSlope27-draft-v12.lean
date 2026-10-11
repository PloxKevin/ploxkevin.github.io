import SafeLearning.CompleteModulesValues
import SafeLearning.CompleteFoundationsGraphViability

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Classical

/-!
TMP future27 draft, not compiled or selected.
The grid follows viability.html's ROWS=5/COLS=8/CLIFF=4,
ACTS=[Up,Down,Left,Right,Stay], source-cell slope slide, and zero-slip semantics.
All cliff coordinates are collapsed to the one failure event, followed by
an explicit zero-reward sink. No candidate return is a hypothesis.
-/
namespace SafeLearning.CompleteAppliedExplorerSlope27

inductive Action where
  | up | down | left | right | stay
  deriving DecidableEq

inductive State where
  | live (row : Fin 4) (col : Fin 8)
  | failure | sink
  deriving DecidableEq

/-- The exact six source-cell slope locations. -/
def slope (row col : ℕ) : Bool :=
  (row == 3 && decide (2 ≤ col ∧ col ≤ 5)) || (row == 2 && (col == 3 || col == 4))

/-- Nat subtraction implements JS's lower clamp for the Up/Left actions. -/
def movedRow (row : ℕ) : Action → ℕ
  | .up => row - 1
  | .down => min 4 (row + 1)
  | _ => row

def movedCol (col : ℕ) : Action → ℕ
  | .left => col - 1
  | .right => min 7 (col + 1)
  | _ => col

def cell (row col : ℕ) : State :=
  .live ⟨min 3 row, by omega⟩ ⟨min 7 col, by omega⟩

def step : State → Action → State
  | .failure, _ => .sink
  | .sink, _ => .sink
  | .live row col, a =>
      let row' := if slope row.val col.val then min 4 (movedRow row.val a + 1)
                    else movedRow row.val a
      let col' := movedCol col.val a
      if row' = 4 then .failure else cell row' col'

def available : State → Action → Prop
  | .live row col, a => slope row.val col.val = false ∨ a ≠ .up
  | _, _ => True

def upper : State := cell 2 3

def lowerLeft : State := cell 3 2

def lowerCenter : State := cell 3 3

def lowerRight : State := cell 3 4

/-- The literal reward function, including zero reward at failure and sink. -/
def reward (cost goalReward : ℝ) : State → ℝ
  | .live row col => if row.val = 3 ∧ col.val = 7 then goalReward else -cost
  | _ => 0

def failureCharge : State → ℝ
  | .failure => 1
  | _ => 0

/-- The post-failure sink is bookkeeping, excluded from the physical world. -/
def world : Set State := {s | s ≠ .sink}

def safeStates : Set State := {s | match s with
  | .live _ _ => True
  | _ => False}

def kernelStates : Set State := {s | match s with
  | .live row col => slope row.val col.val = false
  | _ => False}

def unviableStates : Set State := world \ kernelStates

theorem actual_nonslope_stay_is_safe_self_loop (row : Fin 4) (col : Fin 8)
    (hs : slope row.val col.val = false) :
    step (.live row col) .stay = .live row col := by
  have hr : row.val ≤ 3 := by omega
  have hc : col.val ≤ 7 := by omega
  have hr4 : row.val ≠ 4 := by omega
  simp [step, hs, movedRow, movedCol, cell, hr4,
    Nat.min_eq_right hr, Nat.min_eq_right hc]

set_option maxHeartbeats 2000000 in
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
      clear hY hYs
      fin_cases row <;> fin_cases col <;>
        simp [slope] at hnonslope <;> cases a <;> cases b <;>
        simp_all [safeStates, kernelStates, available, step, cell,
          slope, movedRow, movedCol]
    | failure => simpa [safeStates, kernelStates] using hYs hs
    | sink => simpa [safeStates, kernelStates] using hYs hs

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
    · simpa [reward, hg] using neg_nonpos.mpr hc
  | failure => simp [reward]
  | sink => simp [reward]

theorem actual_unviable_reward_supremum_is_zero (cost goalReward : ℝ) (hc : 0 ≤ cost) :
    sSup (reward cost goalReward '' unviableStates) = 0 := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨.failure, by simp [unviableStates, world, kernelStates], by simp [reward]⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact actual_unviable_reward_is_nonpositive _ _ hc s hs

theorem actual_unviable_state_action_reward_supremum_is_zero
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

def discountedReward (discount cost goalReward : ℝ) (states : ℕ → State) : ℝ :=
  ∑' n, discount ^ n * reward cost goalReward (states n)

def discountedRisk (discount : ℝ) (states : ℕ → State) : ℝ :=
  ∑' n, discount ^ n * failureCharge (states n)

def penalizedReturn (discount cost goalReward penalty : ℝ) (states : ℕ → State) : ℝ :=
  discountedReward discount cost goalReward states - penalty * discountedRisk discount states

/-- Every realized admissible control path, not an asserted list of candidate rewards. -/
def Realizes (states : ℕ → State) (actions : ℕ → Action) : Prop :=
  states 0 = upper ∧
  (∀ n, available (states n) (actions n)) ∧
  ∀ n, states (n + 1) = step (states n) (actions n)

theorem actual_upper_available_iff (a : Action) : available upper a ↔ a ≠ .up := by
  simp [available, upper, cell, slope]

theorem actual_upper_successor_table :
    step upper .down = .failure ∧ step upper .left = lowerLeft ∧
    step upper .right = lowerRight ∧ step upper .stay = lowerCenter := by
  norm_num [step, upper, lowerLeft, lowerRight, lowerCenter, cell, slope,
    movedRow, movedCol]

theorem actual_every_lower_action_falls (s : State) (a : Action)
    (hs : s = lowerLeft ∨ s = lowerCenter ∨ s = lowerRight)
    (ha : available s a) : step s a = .failure := by
  rcases hs with rfl | rfl | rfl <;>
    cases a <;>
    simp_all [available, step, lowerLeft, lowerCenter, lowerRight,
      cell, slope, movedRow, movedCol]

theorem actual_sink_tail (states : ℕ → State) (actions : ℕ → Action) (start : ℕ)
    (hs : states start = .sink)
    (hstep : ∀ n, states (n + 1) = step (states n) (actions n)) :
    ∀ n, start ≤ n → states n = .sink := by
  have htail : ∀ d, states (start + d) = .sink := by
    intro d
    induction d with
    | zero => simpa using hs
    | succ d ih =>
        rw [show start + (d + 1) = (start + d) + 1 by omega, hstep, ih]
        rfl
  intro n hn
  have he : n = start + (n - start) := by omega
  rw [he]
  exact htail _

set_option maxHeartbeats 2000000 in
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
        clear hstep hlegal
        fin_cases row <;> fin_cases col <;>
          simp [hs, unviableStates, world, kernelStates, slope] at hzero <;>
          cases ha0 : actions 0 <;> cases ha1 : actions 1 <;>
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

/-- The literal transition to the sink makes the failure event one-time. -/
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

theorem actual_every_upper_path_has_the_two_failure_patterns
    (states : ℕ → State) (actions : ℕ → Action) (h : Realizes states actions) :
    (actions 0 = .down ∧ states 1 = .failure ∧ ∀ n, 2 ≤ n → states n = .sink) ∨
    (actions 0 ≠ .down ∧
      (states 1 = lowerLeft ∨ states 1 = lowerCenter ∨ states 1 = lowerRight) ∧
      states 2 = .failure ∧ ∀ n, 3 ≤ n → states n = .sink) := by
  rcases h with ⟨hzero, hlegal, hstep⟩
  have hfirst : states 1 = step upper (actions 0) := by simpa [hzero] using hstep 0
  have haction : actions 0 ≠ .up :=
    (actual_upper_available_iff _).mp (by simpa [hzero] using hlegal 0)
  by_cases hd : actions 0 = .down
  · left
    have hfailure : states 1 = .failure := by
      rw [hfirst, hd, actual_upper_successor_table.1]
    have hsink : states 2 = .sink := by
      simpa [hfailure, step] using hstep 1
    exact ⟨hd, hfailure, actual_sink_tail states actions 2 hsink hstep⟩
  · right
    have hlower : states 1 = lowerLeft ∨ states 1 = lowerCenter ∨ states 1 = lowerRight := by
      rw [hfirst]
      cases he : actions 0 <;>
        simp_all [step, upper, lowerLeft, lowerCenter, lowerRight,
          cell, slope, movedRow, movedCol]
    have hfailure : states 2 = .failure := by
      rw [hstep 1]
      exact actual_every_lower_action_falls _ _ hlower (hlegal 1)
    have hsink : states 3 = .sink := by
      simpa [hfailure, step] using hstep 2
    exact ⟨hd, hlower, hfailure, actual_sink_tail states actions 3 hsink hstep⟩

/-- Both infinite sums are genuine finite-support sums of the actual states. -/
theorem actual_three_term_counting_sums
    (discount cost goalReward : ℝ) (states : ℕ → State)
    (htail : ∀ n, 3 ≤ n → states n = .sink) :
    discountedReward discount cost goalReward states =
      reward cost goalReward (states 0) + discount * reward cost goalReward (states 1) +
        discount ^ 2 * reward cost goalReward (states 2) ∧
    discountedRisk discount states =
      failureCharge (states 0) + discount * failureCharge (states 1) +
        discount ^ 2 * failureCharge (states 2) := by
  constructor
  · rw [discountedReward, tsum_eq_sum (s := Finset.range 3)]
    · norm_num [Finset.sum_range_succ]
    · intro n hn
      have hn3 : 3 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      simp [htail n hn3, reward]
  · rw [discountedRisk, tsum_eq_sum (s := Finset.range 3)]
    · norm_num [Finset.sum_range_succ]
    · intro n hn
      have hn3 : 3 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      simp [htail n hn3, failureCharge]

theorem actual_every_upper_path_return_is_fast_or_slow
    (discount cost goalReward penalty : ℝ) (states : ℕ → State) (actions : ℕ → Action)
    (h : Realizes states actions) :
    penalizedReturn discount cost goalReward penalty states = -cost - discount * penalty ∨
    penalizedReturn discount cost goalReward penalty states =
      -cost - discount * cost - discount ^ 2 * penalty := by
  have hzero := h.1
  rcases actual_every_upper_path_has_the_two_failure_patterns states actions h with
    ⟨_, hfailure, htail⟩ | ⟨_, hlower, hfailure, htail⟩
  · left
    have hsink : states 2 = .sink := htail 2 (by omega)
    have hsums := actual_three_term_counting_sums discount cost goalReward states
      (fun n hn => htail n (by omega))
    rw [penalizedReturn, hsums.1, hsums.2, hzero, hfailure, hsink]
    norm_num [reward, failureCharge, upper, cell] <;> ring
  · right
    have hsums := actual_three_term_counting_sums discount cost goalReward states htail
    rw [penalizedReturn, hsums.1, hsums.2, hzero, hfailure]
    rcases hlower with hleft | hcenter | hright <;>
      simp_all [reward, failureCharge,
        upper, lowerLeft, lowerCenter, lowerRight, cell] <;> ring

structure Feedback where
  choose : State → Action
  legal : ∀ s, available s (choose s)

def feedbackStates (controller : Feedback) : ℕ → State
  | 0 => upper
  | n + 1 => step (feedbackStates controller n) (controller.choose (feedbackStates controller n))

def feedbackActions (controller : Feedback) (n : ℕ) : Action :=
  controller.choose (feedbackStates controller n)

def downFeedback : Feedback :=
  ⟨fun _ => .down, by intro s; cases s <;> simp [available]⟩

def stayFeedback : Feedback :=
  ⟨fun _ => .stay, by intro s; cases s <;> simp [available]⟩

def controllerReturn (discount cost goalReward penalty : ℝ) (controller : Feedback) : ℝ :=
  penalizedReturn discount cost goalReward penalty (feedbackStates controller)

def actualUpperValue (discount cost goalReward penalty : ℝ) : ℝ :=
  sSup (Set.range (controllerReturn discount cost goalReward penalty))

theorem actual_every_feedback_realizes_its_path (controller : Feedback) :
    Realizes (feedbackStates controller) (feedbackActions controller) := by
  exact ⟨rfl, fun n => controller.legal _, fun _ => rfl⟩

theorem actual_down_feedback_attains_fast (discount cost goalReward penalty : ℝ) :
    controllerReturn discount cost goalReward penalty downFeedback = -cost - discount * penalty := by
  have hsink : ∀ n, 2 ≤ n → feedbackStates downFeedback n = .sink :=
    actual_sink_tail _ _ 2 (by
      norm_num [feedbackStates, downFeedback, step, upper, cell, slope, movedRow, movedCol])
      (actual_every_feedback_realizes_its_path downFeedback).2.2
  have hsums := actual_three_term_counting_sums discount cost goalReward (feedbackStates downFeedback)
    (fun n hn => hsink n (by omega))
  rw [controllerReturn, penalizedReturn, hsums.1, hsums.2]
  norm_num [feedbackStates, downFeedback, reward, failureCharge, step,
    upper, cell, slope, movedRow, movedCol] <;> ring

theorem actual_stay_feedback_attains_slow (discount cost goalReward penalty : ℝ) :
    controllerReturn discount cost goalReward penalty stayFeedback =
      -cost - discount * cost - discount ^ 2 * penalty := by
  have hsink : ∀ n, 3 ≤ n → feedbackStates stayFeedback n = .sink :=
    actual_sink_tail _ _ 3 (by
      norm_num [feedbackStates, stayFeedback, step, upper, cell, slope, movedRow, movedCol])
      (actual_every_feedback_realizes_its_path stayFeedback).2.2
  have hsums := actual_three_term_counting_sums discount cost goalReward (feedbackStates stayFeedback) hsink
  rw [controllerReturn, penalizedReturn, hsums.1, hsums.2]
  norm_num [feedbackStates, stayFeedback, reward, failureCharge, step,
    upper, cell, slope, movedRow, movedCol]
  ring

theorem actual_controller_return_set_is_exactly_the_two_source_values
    (discount cost goalReward penalty : ℝ) :
    Set.range (controllerReturn discount cost goalReward penalty) =
      {-cost - discount * penalty, -cost - discount * cost - discount ^ 2 * penalty} := by
  ext v
  constructor
  · rintro ⟨controller, rfl⟩
    have hv := actual_every_upper_path_return_is_fast_or_slow discount cost goalReward penalty
      (feedbackStates controller) (feedbackActions controller)
      (actual_every_feedback_realizes_its_path controller)
    simpa [controllerReturn, Set.mem_insert_iff, Set.mem_singleton_iff] using hv
  · intro hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨downFeedback, actual_down_feedback_attains_fast _ _ _ _⟩
    · exact ⟨stayFeedback, actual_stay_feedback_attains_slow _ _ _ _⟩

theorem actual_controller_supremum_is_attained_source_max
    (discount cost goalReward penalty : ℝ) :
    actualUpperValue discount cost goalReward penalty =
      max (-cost - discount * penalty) (-cost - discount * cost - discount ^ 2 * penalty) := by
  unfold actualUpperValue
  rw [actual_controller_return_set_is_exactly_the_two_source_values]
  exact csSup_pair _ _

theorem actual_stopped_reward_and_negative_bound_difference (discount cost penalty : ℝ) :
    (-cost - discount * cost - discount ^ 2 * penalty) -
      (-cost * (1 + discount + discount ^ 2) - penalty * discount ^ 2) = discount ^ 2 * cost ∧
    -cost + discount * (-cost - discount * penalty) =
      -cost - discount * cost - discount ^ 2 * penalty := by
  constructor <;> ring

theorem actual_slope_value_has_the_source_bound (discount cost goalReward penalty : ℝ)
    (hd : 0 ≤ discount) (hd1 : discount ≤ 1) (hc : 0 ≤ cost) (hp : 0 ≤ penalty) :
    actualUpperValue discount cost goalReward penalty ≤ -penalty * discount ^ 2 := by
  rw [actual_controller_supremum_is_attained_source_max]
  exact CompleteModulesValues.two_step_slope_bound _ _ _ hd hd1 hc hp

theorem actual_slow_fall_strictly_wins_exactly_when_printed
    (discount cost goalReward penalty : ℝ) (hd : 0 < discount) :
    controllerReturn discount cost goalReward penalty downFeedback <
      controllerReturn discount cost goalReward penalty stayFeedback ↔ cost < penalty * (1 - discount) := by
  rw [actual_down_feedback_attains_fast, actual_stay_feedback_attains_slow]
  exact CompleteModulesValues.slow_slope_strictly_better _ _ _ hd

theorem actual_nonnegative_reward_constant (cost : ℝ) (hc : 0 ≤ cost) :
    max 0 (-cost) = 0 := by simp [max_eq_left (by linarith : -cost ≤ 0)]

theorem actual_negative_reward_bound_is_below_the_value
    (discount cost goalReward penalty : ℝ) (hd : 0 < discount) (hc : 0 < cost) :
    -cost * (1 + discount + discount ^ 2) - penalty * discount ^ 2 <
      actualUpperValue discount cost goalReward penalty := by
  rw [actual_controller_supremum_is_attained_source_max]
  exact lt_of_lt_of_le (CompleteModulesValues.negative_reward_slope_bound_false _ _ _ hd hc)
    (le_max_right _ _)

/-- A stopped sequence has the counting-measure reward exactly as printed. -/
theorem stopped_discounted_reward_is_finite_prefix (discount : ℝ) (rewards : ℕ → ℝ)
    (failure : ℕ) (hz : ∀ n, failure < n → rewards n = 0) :
    (∑' n, discount ^ n * rewards n) =
      ∑ n ∈ Finset.range (failure + 1), discount ^ n * rewards n := by
  apply tsum_eq_sum
  intro n hn
  have hnf : failure < n := by
    have hn' : ¬n < failure + 1 := by simpa only [Finset.mem_range] using hn
    omega
  simp [hz n hnf]

/-- Finite support derives integrability, rather than making it an assumption. -/
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
  simp only [count_real_singleton, one_smul]
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

theorem single_failure_discounted_risk_is_arrival_weight (discount : ℝ) (failure : ℕ) :
    (∑' n : ℕ, discount ^ n * (if n = failure then 1 else 0 : ℝ)) = discount ^ failure := by
  rw [tsum_eq_single failure]
  · simp
  · intro n hn
    simp [hn]

theorem actual_single_failure_counting_integral_is_arrival_weight
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
  simp only [count_real_singleton, one_smul]
  exact single_failure_discounted_risk_is_arrival_weight _ _

/-- No one-time-charge or vanishing-tail assumption is needed for this actual grid path. -/
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

theorem nonnegative_reward_bound_allows_horizon_extension
    (discount bound : ℝ) (failure horizon : ℕ) (hd : 0 ≤ discount)
    (hb : 0 ≤ bound) (ht : failure ≤ horizon) :
    bound * (∑ n ∈ Finset.range (failure + 1), discount ^ n) ≤
      bound * (∑ n ∈ Finset.range (horizon + 1), discount ^ n) := by
  apply mul_le_mul_of_nonneg_left _ hb
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (by intros; positivity)

theorem negative_reward_bound_reverses_horizon_extension
    (discount bound : ℝ) (failure horizon : ℕ) (hd : 0 ≤ discount)
    (hb : bound ≤ 0) (ht : failure ≤ horizon) :
    bound * (∑ n ∈ Finset.range (horizon + 1), discount ^ n) ≤
      bound * (∑ n ∈ Finset.range (failure + 1), discount ^ n) := by
  apply mul_le_mul_of_nonpos_left _ hb
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (by intros; positivity)

theorem counting_sum_doomed_return_bound (discount bound penalty : ℝ)
    (rewards : ℕ → ℝ) (failure horizon : ℕ) (hd : 0 ≤ discount) (hd1 : discount < 1)
    (hb : 0 ≤ bound) (hp : 0 ≤ penalty) (ht : failure ≤ horizon)
    (hr : ∀ n < failure + 1, rewards n ≤ bound)
    (hz : ∀ n, failure < n → rewards n = 0) :
    (∑' n, discount ^ n * rewards n) -
      penalty * (∑' n : ℕ, discount ^ n * (if n = failure then 1 else 0 : ℝ)) ≤
      bound * (1 - discount ^ (horizon + 1)) / (1 - discount) - penalty * discount ^ horizon := by
  rw [stopped_discounted_reward_is_finite_prefix discount rewards failure hz,
    single_failure_discounted_risk_is_arrival_weight]
  exact CompleteModulesValues.finite_discounted_doomed_bound _ _ _ _ _ _ hd hd1 hb hp ht hr

/-- Adding a safe predecessor of the greatest invariant set cannot enlarge it. -/
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
  simp_rw [hfailure]
  apply counting_sum_doomed_return_bound _ _ _ _ _ _ hd hd1 hb hp ht
  · intro n hn
    exact hr (states n) (hvisited n (by omega)) (actions n) (hallowed n)
  · exact hz

theorem both_controller_and_state_suprema_preserve_counting_sum_bound
    {X Controller : Type*} [Nonempty X] [Nonempty Controller]
    (discount bound penalty : ℝ) (rewards : X → Controller → ℕ → ℝ)
    (failure : X → Controller → ℕ) (horizon : ℕ)
    (hd : 0 ≤ discount) (hd1 : discount < 1) (hb : 0 ≤ bound) (hp : 0 ≤ penalty)
    (ht : ∀ x u, failure x u ≤ horizon)
    (hr : ∀ x u n, n < failure x u + 1 → rewards x u n ≤ bound)
    (hz : ∀ x u n, failure x u < n → rewards x u n = 0) :
    sSup (Set.range (fun x => sSup (Set.range (fun u =>
      (∑' n, discount ^ n * rewards x u n) - penalty *
        (∑' n : ℕ, discount ^ n * (if n = failure x u then 1 else 0 : ℝ)))))) ≤
      bound * (1 - discount ^ (horizon + 1)) / (1 - discount) - penalty * discount ^ horizon := by
  apply CompleteModulesValues.supremum_doomed_bound
  · exact Set.range_nonempty _
  · intro x
    apply CompleteModulesValues.supremum_doomed_bound
    · exact Set.range_nonempty _
    · intro u
      exact counting_sum_doomed_return_bound _ _ _ _ _ _ hd hd1 hb hp (ht x u)
        (hr x u) (hz x u)

/-- This is the source supremum convention even when the unviable set is empty.
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
        (∑' n : ℕ, discount ^ n * (if n = failure x u then 1 else 0 : ℝ)))) : ℝ) : EReal))) ≤
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

end SafeLearning.CompleteAppliedExplorerSlope27


namespace SafeLearning.CompleteAppliedExplorerSlope27

/-- The source reward supremum is over physical unviable states, not the
post-failure bookkeeping sink. Boundedness comes from the source reward scope. -/
theorem actual_reward_supremum_bounds_each_physical_unviable_state_action
    {S A : Type*} (physical kernel : Set S) (r : S → A → ℝ)
    (hbounded : BddAbove (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)))
    (x : S) (hx : x ∈ physical) (hxk : x ∉ kernel) (a : A) :
    r x a ≤ sSup (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)) := by
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
    (hbounded : BddAbove (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)))
    (hsup : sSup (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)) ≤ bound)
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
    (hbounded : BddAbove (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)))
    (hsup : sSup (Set.range (fun q : {s : S // s ∈ physical ∧ s ∉ kernel} × A => r q.1.val q.2)) ≤ bound)
    (hz : ∀ x u n, failure x u < n → r (states x u n) (actions x u n) = 0)
    (hfailure : ∀ x u n, states x u n ∈ failureStates ↔ n = failure x u) :
    sSup (Set.range (fun x => ((sSup (Set.range (fun u =>
      (∑' n, discount ^ n * r (states x u n) (actions x u n)) - penalty *
        (∑' n : ℕ, discount ^ n * (if states x u n ∈ failureStates then 1 else 0 : ℝ)))) : ℝ) : EReal))) ≤
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
