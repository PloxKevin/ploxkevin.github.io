import SafeLearning.CompleteFoundationsTelescopingApplications
import SafeLearning.CompleteModulesBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteModulesThermalPenaltyBellmanWhole30
open CompleteFoundationsTelescopingApplications CompleteFoundationsLessonSeries

section GenuineInfiniteDiscountedReturns
variable {S A : Type*} [Fintype S] [Fintype A]

def finiteAbsoluteBound {T : Type*} [Fintype T] (f : T → ℝ) : ℝ :=
  ∑ t, |f t|

theorem actual_finite_function_has_a_uniform_absolute_bound
    {T : Type*} [Fintype T] (f : T → ℝ) (t : T) :
    |f t| ≤ finiteAbsoluteBound f := by
  exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ t)

def actualReturn (γ : ℝ) (reward : S → A → ℝ) (state : ℕ → S)
    (action : ℕ → A) : ℝ := ∑' n, γ ^ n * reward (state n) (action n)

theorem actual_every_finite_state_reward_path_has_a_summable_discounted_return
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (reward : S → A → ℝ)
    (state : ℕ → S) (action : ℕ → A) :
    Summable (fun n => γ ^ n * reward (state n) (action n)) := by
  exact (actual_bounded_discounted_return_and_tail γ
    (finiteAbsoluteBound (fun z : S × A => reward z.1 z.2))
    (fun n => reward (state n) (action n)) hγ0 hγ1
    (fun n => actual_finite_function_has_a_uniform_absolute_bound (fun z : S × A => reward z.1 z.2) (state n, action n)) 0).1

theorem actual_bellman_upper_bound_bounds_every_history_dependent_return
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (next : S → A → S)
    (allowed : S → A → Prop) (reward : S → A → ℝ) (value : S → ℝ)
    (hbellman : ∀ s a, allowed s a → reward s a + γ * value (next s a) ≤ value s)
    (state : ℕ → S) (action : ℕ → A)
    (hpath : ∀ n, allowed (state n) (action n) ∧ state (n + 1) = next (state n) (action n)) :
    actualReturn γ reward state action ≤ value (state 0) := by
  have ht := actual_discounted_td_partial_sums_have_the_true_infinite_limit γ
    (finiteAbsoluteBound (fun z : S × A => reward z.1 z.2)) (finiteAbsoluteBound value)
    hγ0 hγ1 (fun n => reward (state n) (action n)) (fun n => value (state n))
    (fun n => actual_finite_function_has_a_uniform_absolute_bound (fun z : S × A => reward z.1 z.2) (state n, action n))
    (fun n => actual_finite_function_has_a_uniform_absolute_bound _ (state n))
  have hn (N : ℕ) : (∑ n ∈ Finset.range N, γ ^ n *
      (reward (state n) (action n) + γ * value (state (n + 1)) - value (state n))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro n _
    apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ0 n)
    rw [(hpath n).2]
    linarith [hbellman (state n) (action n) (hpath n).1]
  have h := le_of_tendsto ht (Eventually.of_forall hn)
  change actualReturn γ reward state action - value (state 0) ≤ 0 at h
  linarith

theorem actual_every_bellman_equality_path_attains_the_infinite_return
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (next : S → A → S)
    (reward : S → A → ℝ) (value : S → ℝ) (state : ℕ → S) (action : ℕ → A)
    (hpath : ∀ n, state (n + 1) = next (state n) (action n))
    (heq : ∀ n, reward (state n) (action n) + γ * value (next (state n) (action n)) = value (state n)) :
    actualReturn γ reward state action = value (state 0) := by
  have hup := actual_bellman_upper_bound_bounds_every_history_dependent_return γ hγ0 hγ1
    next (fun s a => reward s a + γ * value (next s a) = value s) reward value
    (fun _ _ h => h.le) state action (fun n => ⟨heq n, hpath n⟩)
  have hlo := actual_bellman_upper_bound_bounds_every_history_dependent_return γ hγ0 hγ1
    next (fun s a => reward s a + γ * value (next s a) = value s)
    (fun s a => -reward s a) (fun s => -value s)
    (fun s a h => by linarith) state action (fun n => ⟨heq n, hpath n⟩)
  have hn : actualReturn γ (fun s a => -reward s a) state action = -actualReturn γ reward state action := by
    unfold actualReturn
    simp only [mul_neg, tsum_neg]
  rw [hn] at hlo
  linarith

theorem actual_infinite_return_keeps_the_first_action_and_true_tail
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (reward : S → A → ℝ)
    (state : ℕ → S) (action : ℕ → A) :
    actualReturn γ reward state action = reward (state 0) (action 0) +
      γ * actualReturn γ reward (fun n => state (n + 1)) (fun n => action (n + 1)) := by
  have hs := actual_every_finite_state_reward_path_has_a_summable_discounted_return γ hγ0 hγ1 reward state action
  unfold actualReturn
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

end GenuineInfiniteDiscountedReturns

-- State indices 0,1,2,3,4 are temperatures 52,54,56,58,60; index 5 is absorbing failure.
abbrev ThermalState := Fin 6
def temperature (s : ThermalState) : ℝ := 52 + 2 * (s.val : ℝ)
def thermalNext (s : ThermalState) (run : Bool) : ThermalState :=
  if run then ![1,2,3,4,5,5] s else ![5,5,0,1,5,5] s
def thermalAllowed (s : ThermalState) (run : Bool) : Prop := s ≠ 4 ∨ run = true
def thermalReward (p : ℝ) (s : ThermalState) (run : Bool) : ℝ :=
  if run then ![3,3,3,25,3-p,0] s else ![-p,-p,0,0,0,0] s
def thermalViable (s : ThermalState) : Prop := s.val < 4
def trajectory (initial : ThermalState) (policy : ThermalState → Bool) : ℕ → ThermalState
  | 0 => initial
  | n + 1 => thermalNext (trajectory initial policy n) (policy (trajectory initial policy n))
def cyclePolicy (s : ThermalState) : Bool := decide (s ≠ 3)
def safeValue8 (p : ℝ) : ThermalState → ℝ := ![723/61,675/61,615/61,540/61,3-p,0]
def strictThreshold8 : ℝ := 5657/244
def rush8 (p : ℝ) : ℝ := 25 + (4/5) * (3-p)
def actionValue8 (p : ℝ) (s : ThermalState) (a : Bool) : ℝ :=
  thermalReward p s a + (4/5) * safeValue8 p (thermalNext s a)
def optimalAction8 (p : ℝ) (s : ThermalState) (a : Bool) : Prop :=
  thermalAllowed s a ∧ ∀ b, thermalAllowed s b → actionValue8 p s b ≤ actionValue8 p s a

theorem actual_temperature_and_transition_indices :
    temperature 0 = 52 ∧ temperature 1 = 54 ∧ temperature 2 = 56 ∧
    temperature 3 = 58 ∧ temperature 4 = 60 ∧
    thermalNext 3 false = 1 ∧ thermalNext 1 true = 2 ∧ thermalNext 2 true = 3 ∧
    thermalNext 3 true = 4 ∧ thermalNext 4 true = 5 ∧
    ¬thermalAllowed 4 false := by
  norm_num [temperature,thermalNext,thermalAllowed]

theorem actual_cycle_policy_is_allowed_everywhere (s : ThermalState) :
    thermalAllowed s (cyclePolicy s) := by
  fin_cases s <;> norm_num [thermalAllowed,cyclePolicy]

theorem actual_cycle_policy_preserves_every_viable_state (s : ThermalState)
    (hs : thermalViable s) : thermalViable (thermalNext s (cyclePolicy s)) := by
  fin_cases s <;> simp_all [thermalViable,thermalNext,cyclePolicy]

theorem actual_cycle_trajectory_is_safe_at_all_times (initial : ThermalState)
    (hi : thermalViable initial) : ∀ n, thermalViable (trajectory initial cyclePolicy n) := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih => exact actual_cycle_policy_preserves_every_viable_state _ ih

theorem actual_complete_discounted_cycle_is_a_bellman_equality (p : ℝ) (s : ThermalState) :
    actionValue8 p s (cyclePolicy s) = safeValue8 p s := by
  fin_cases s <;> norm_num [actionValue8,safeValue8,thermalNext,thermalReward,cyclePolicy]

theorem actual_threshold_gives_a_global_bellman_upper_bound
    (p : ℝ) (hp : strictThreshold8 ≤ p) (s : ThermalState) (a : Bool)
    (ha : thermalAllowed s a) : actionValue8 p s a ≤ safeValue8 p s := by
  fin_cases s <;> cases a <;>
    simp_all [actionValue8,safeValue8,thermalNext,thermalReward,thermalAllowed] <;>
    norm_num [strictThreshold8] at * <;> linarith

theorem actual_all_admissible_history_returns_are_bounded_by_the_cycle_value
    (p : ℝ) (hp : strictThreshold8 ≤ p) (state : ℕ → ThermalState) (action : ℕ → Bool)
    (hpath : ∀ n, thermalAllowed (state n) (action n) ∧ state (n+1) = thermalNext (state n) (action n)) :
    actualReturn (4/5) (thermalReward p) state action ≤ safeValue8 p (state 0) := by
  exact actual_bellman_upper_bound_bounds_every_history_dependent_return (4/5) (by norm_num) (by norm_num)
    thermalNext thermalAllowed (thermalReward p) (safeValue8 p)
    (actual_threshold_gives_a_global_bellman_upper_bound p hp) state action hpath

theorem actual_cycle_path_attains_the_complete_infinite_discounted_value
    (p : ℝ) (initial : ThermalState) :
    actualReturn (4/5) (thermalReward p) (trajectory initial cyclePolicy)
      (fun n => cyclePolicy (trajectory initial cyclePolicy n)) = safeValue8 p initial := by
  have he := actual_every_bellman_equality_path_attains_the_infinite_return (4/5) (by norm_num) (by norm_num)
    thermalNext (thermalReward p) (safeValue8 p) (trajectory initial cyclePolicy)
    (fun n => cyclePolicy (trajectory initial cyclePolicy n)) (fun _ => rfl)
    (fun n => actual_complete_discounted_cycle_is_a_bellman_equality p _)
  exact he

theorem actual_cycle_is_the_attained_optimum_over_every_admissible_history
    (p : ℝ) (hp : strictThreshold8 ≤ p) (initial : ThermalState) :
    IsGreatest {v : ℝ | ∃ state : ℕ → ThermalState, ∃ action : ℕ → Bool,
      state 0 = initial ∧
      (∀ n, thermalAllowed (state n) (action n) ∧ state (n+1)=thermalNext (state n) (action n)) ∧
      actualReturn (4/5) (thermalReward p) state action = v} (safeValue8 p initial) := by
  refine ⟨?_,?_⟩
  · exact ⟨trajectory initial cyclePolicy, fun n => cyclePolicy (trajectory initial cyclePolicy n),
      rfl, fun n => ⟨actual_cycle_policy_is_allowed_everywhere _, rfl⟩,
      actual_cycle_path_attains_the_complete_infinite_discounted_value p initial⟩
  · rintro v ⟨state,action,h0,hpath,rfl⟩
    simpa only [h0] using actual_all_admissible_history_returns_are_bounded_by_the_cycle_value p hp state action hpath

theorem actual_safe_cooling_and_unsafe_rush_action_values (p : ℝ) :
    actionValue8 p 3 false = 540/61 ∧ actionValue8 p 3 true = rush8 p := by
  norm_num [actionValue8,safeValue8,thermalNext,thermalReward,rush8]

theorem actual_all_bellman_maximizing_actions_at58_are_safe_iff_strict_penalty
    (p : ℝ) :
    (∀ a, optimalAction8 p 3 a → a = false) ↔ strictThreshold8 < p := by
  have hvalues := actual_safe_cooling_and_unsafe_rush_action_values p
  constructor
  · intro hall
    by_contra hp
    have hle : p ≤ strictThreshold8 := le_of_not_gt hp
    have hrush : optimalAction8 p 3 true := by
      refine ⟨by norm_num [thermalAllowed],?_⟩
      intro b _
      cases b
      · rw [hvalues.1,hvalues.2]
        dsimp [rush8,strictThreshold8] at hle ⊢
        linarith
      · exact le_rfl
    exact Bool.noConfusion (hall true hrush)
  · intro hp a ha
    cases a
    · rfl
    · have h := ha.2 false (by norm_num [thermalAllowed])
      rw [hvalues.1,hvalues.2] at h
      dsimp [rush8,strictThreshold8] at h hp
      linarith

theorem actual_boundary_has_both_a_safe_and_an_unsafe_maximizing_action :
    optimalAction8 strictThreshold8 3 false ∧ optimalAction8 strictThreshold8 3 true ∧
    thermalViable (thermalNext 3 false) ∧ ¬thermalViable (thermalNext 3 true) := by
  have heq : actionValue8 strictThreshold8 3 false = actionValue8 strictThreshold8 3 true := by
    norm_num [strictThreshold8,actionValue8,safeValue8,thermalNext,thermalReward]
  refine ⟨⟨by norm_num [thermalAllowed],?_⟩,⟨by norm_num [thermalAllowed],?_⟩,
    by norm_num [thermalViable,thermalNext],by norm_num [thermalViable,thermalNext]⟩
  · intro b _
    cases b
    · exact le_rfl
    · exact heq.symm.le
  · intro b _
    cases b
    · exact heq.le
    · exact le_rfl

theorem actual_penalty24_is_strict_and_every_maximizing_action_cools :
    strictThreshold8 < 24 ∧ rush8 24 = 41/5 ∧ 41/5 < (540/61 : ℝ) ∧
    ∀ a, optimalAction8 24 3 a → a = false := by
  refine ⟨by norm_num [strictThreshold8],by norm_num [rush8],by norm_num,?_⟩
  exact (actual_all_bellman_maximizing_actions_at58_are_safe_iff_strict_penalty 24).mpr
    (by norm_num [strictThreshold8])

theorem actual_every_infinite_return_maximizer_at58_must_cool
    (p : ℝ) (hp : strictThreshold8 < p) (state : ℕ → ThermalState) (action : ℕ → Bool)
    (h0 : state 0 = 3)
    (hpath : ∀ n, thermalAllowed (state n) (action n) ∧ state (n+1)=thermalNext (state n) (action n))
    (hoptimal : actualReturn (4/5) (thermalReward p) state action = 540/61) :
    action 0 = false := by
  have ht := actual_all_admissible_history_returns_are_bounded_by_the_cycle_value p hp.le
    (fun n => state (n+1)) (fun n => action (n+1)) (fun n => hpath (n+1))
  have hsplit := actual_infinite_return_keeps_the_first_action_and_true_tail (4/5) (by norm_num) (by norm_num)
    (thermalReward p) state action
  cases ha : action 0
  · rfl
  · have h1 : state 1 = 4 := by simpa [h0,ha,thermalNext] using (hpath 0).2
    rw [h1] at ht
    rw [hoptimal,h0,ha] at hsplit
    norm_num [safeValue8,thermalReward] at ht hsplit
    dsimp [strictThreshold8] at hp
    linarith

def boundaryRushPolicy (_s : ThermalState) : Bool := true

theorem actual_boundary_rush_policy_is_an_unsafe_infinite_return_maximizer :
    actualReturn (4/5) (thermalReward strictThreshold8) (trajectory 3 boundaryRushPolicy)
      (fun n => boundaryRushPolicy (trajectory 3 boundaryRushPolicy n)) = 540/61 ∧
    trajectory 3 boundaryRushPolicy 1 = 4 ∧ trajectory 3 boundaryRushPolicy 2 = 5 := by
  have heq : ∀ n, thermalReward strictThreshold8 (trajectory 3 boundaryRushPolicy n)
      (boundaryRushPolicy (trajectory 3 boundaryRushPolicy n)) +
      (4/5) * safeValue8 strictThreshold8
        (thermalNext (trajectory 3 boundaryRushPolicy n) (boundaryRushPolicy (trajectory 3 boundaryRushPolicy n))) =
      safeValue8 strictThreshold8 (trajectory 3 boundaryRushPolicy n) := by
    intro n
    have hstate : trajectory 3 boundaryRushPolicy n = 3 ∨
        trajectory 3 boundaryRushPolicy n = 4 ∨ trajectory 3 boundaryRushPolicy n = 5 := by
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rcases ih with h|h|h <;> simp [trajectory,h,boundaryRushPolicy,thermalNext]
    rcases hstate with h|h|h <;>
      norm_num [h,boundaryRushPolicy,thermalReward,thermalNext,safeValue8,strictThreshold8]
  refine ⟨?_,by norm_num [trajectory,boundaryRushPolicy,thermalNext],
    by norm_num [trajectory,boundaryRushPolicy,thermalNext]⟩
  have he := actual_every_bellman_equality_path_attains_the_infinite_return (4/5) (by norm_num) (by norm_num)
    thermalNext (thermalReward strictThreshold8) (safeValue8 strictThreshold8)
    (trajectory 3 boundaryRushPolicy) (fun n => boundaryRushPolicy (trajectory 3 boundaryRushPolicy n))
    (fun _ => rfl) heq
  simpa [trajectory,safeValue8] using he

theorem actual_printed_threshold_and_cycle_round_to_six_decimals :
    |(540/61 : ℝ) - 8852459/1000000| < 1/2000000 ∧
    |strictThreshold8 - 23184426/1000000| < 1/2000000 ∧
    CompleteModulesBook.safeCycleReturn (4/5) = 540/61 ∧
    ((25:ℝ)+3*(4/5)-CompleteModulesBook.safeCycleReturn (4/5))/(4/5) = strictThreshold8 := by
  norm_num [strictThreshold8,CompleteModulesBook.safeCycleReturn]

end SafeLearning.CompleteModulesThermalPenaltyBellmanWhole30
