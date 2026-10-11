import SafeLearning.CompleteModulesValues

set_option autoImplicit false
noncomputable section
open Set

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
  deriving DecidableEq, Fintype

inductive State where
  | live (row : Fin 4) (col : Fin 8)
  | failure | sink
  deriving DecidableEq, Fintype

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
    norm_num [reward, failureCharge, upper, cell]
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
    upper, cell, slope, movedRow, movedCol]

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

theorem single_failure_discounted_risk_is_arrival_weight (discount : ℝ) (failure : ℕ) :
    (∑' n : ℕ, discount ^ n * (if n = failure then 1 else 0 : ℝ)) = discount ^ failure := by
  rw [tsum_eq_single failure]
  · simp
  · intro n hn
    simp [hn]

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

end SafeLearning.CompleteAppliedExplorerSlope27
