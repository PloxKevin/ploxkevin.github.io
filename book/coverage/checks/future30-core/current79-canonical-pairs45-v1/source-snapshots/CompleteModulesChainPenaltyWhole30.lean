import SafeLearning.CompleteFoundationsTelescopingApplications
import SafeLearning.CompleteModulesBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteModulesChainPenaltyWhole30
open CompleteFoundationsTelescopingApplications CompleteFoundationsLessonSeries

section GenuineInfiniteDiscountedReturns
variable {S A : Type*} [Fintype S] [Fintype A]

def finiteAbsoluteBound {T : Type*} [Fintype T] (f : T → ℝ) : ℝ :=
  ∑ t, |f t|

theorem actual_finite_function_has_a_uniform_absolute_bound
    {T : Type*} [Fintype T] (f : T → ℝ) (t : T) :
    |f t|  ≤  finiteAbsoluteBound f := by
  exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ t)

def actualReturn (γ : ℝ) (reward : S → A → ℝ) (state : ℕ → S)
    (action : ℕ → A) : ℝ := ∑' n, γ ^ n * reward (state n) (action n)

theorem actual_every_finite_state_reward_path_has_a_summable_discounted_return
    (γ : ℝ) (hγ0 : 0  ≤  γ) (hγ1 : γ < 1) (reward : S → A → ℝ)
    (state : ℕ → S) (action : ℕ → A) :
    Summable (fun n => γ ^ n * reward (state n) (action n)) := by
  exact (actual_bounded_discounted_return_and_tail γ
    (finiteAbsoluteBound (fun z : S × A => reward z.1 z.2))
    (fun n => reward (state n) (action n)) hγ0 hγ1
    (fun n => actual_finite_function_has_a_uniform_absolute_bound (fun z : S × A => reward z.1 z.2) (state n, action n)) 0).1

theorem actual_bellman_upper_bound_bounds_every_history_dependent_return
    (γ : ℝ) (hγ0 : 0  ≤  γ) (hγ1 : γ < 1) (next : S → A → S)
    (allowed : S → A → Prop) (reward : S → A → ℝ) (value : S → ℝ)
    (hbellman : ∀ s a, allowed s a → reward s a + γ * value (next s a)  ≤  value s)
    (state : ℕ → S) (action : ℕ → A)
    (hpath : ∀ n, allowed (state n) (action n) ∧ state (n + 1) = next (state n) (action n)) :
    actualReturn γ reward state action  ≤  value (state 0) := by
  have ht := actual_discounted_td_partial_sums_have_the_true_infinite_limit γ
    (finiteAbsoluteBound (fun z : S × A => reward z.1 z.2)) (finiteAbsoluteBound value)
    hγ0 hγ1 (fun n => reward (state n) (action n)) (fun n => value (state n))
    (fun n => actual_finite_function_has_a_uniform_absolute_bound (fun z : S × A => reward z.1 z.2) (state n, action n))
    (fun n => actual_finite_function_has_a_uniform_absolute_bound _ (state n))
  have hn (N : ℕ) : (∑ n ∈ Finset.range N, γ ^ n *
      (reward (state n) (action n) + γ * value (state (n + 1)) - value (state n)))  ≤  0 := by
    apply Finset.sum_nonpos
    intro n _
    apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ0 n)
    rw [(hpath n).2]
    linarith [hbellman (state n) (action n) (hpath n).1]
  have h := le_of_tendsto ht (Eventually.of_forall hn)
  change actualReturn γ reward state action - value (state 0)  ≤  0 at h
  linarith

theorem actual_every_bellman_equality_path_attains_the_infinite_return
    (γ : ℝ) (hγ0 : 0  ≤  γ) (hγ1 : γ < 1) (next : S → A → S)
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
    (γ : ℝ) (hγ0 : 0  ≤  γ) (hγ1 : γ < 1) (reward : S → A → ℝ)
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


-- The original cliff cell is represented once at index0 to collect its one-time penalty,
-- then at index7 for zero future reward. Both project to the same absorbing physical cell0.
abbrev ChainState:=Fin 8
abbrev ChainAction:=Fin 3

def physicalCell (s : ChainState) : Fin 7:=if h:s.val=7 then 0 else ⟨s.val,by omega⟩
def chainNext (s : ChainState) (a : ChainAction) : ChainState:=
  if a=0 then ![7,0,1,2,3,4,5,7] s
  else if a=1 then ![7,0,3,4,5,6,6,7] s else ![7,0,2,3,4,5,6,7] s
def chainAllowed (s : ChainState) (a : ChainAction) : Prop:=s≠6 ∨ a=2
def chainBaseReward (s : ChainState) : ℝ:=![0,-1,-1,-1,-1,-1,1,0] s
def chainReward (p : ℝ) (s : ChainState) (_a : ChainAction) : ℝ:=
  chainBaseReward s-if s=0 then p else 0
def chainViable (s : ChainState) : Prop:=2 ≤ s.val ∧ s.val ≤ 6
def chainTrajectory (initial : ChainState) (policy : ChainState→ChainAction) : ℕ→ChainState
  | 0 => initial
  | n + 1 => chainNext (chainTrajectory initial policy n) (policy (chainTrajectory initial policy n))
def walkPolicy (s : ChainState) : ChainAction:=if s=6 then 2 else 1
def leftPolicy (_s : ChainState) : ChainAction:=0
def safeHalf (p : ℝ) : ChainState→ℝ:=![-p,-1-p/2,-7/4,-3/2,-1,0,2,0]
def leftHalf (p : ℝ) : ChainState→ℝ:=![-p,-1-p/2,-3/2-p/4,-7/4-p/8,-15/8-p/16,-31/16-p/32,1/32-p/64,0]
def bestHalf (p : ℝ) : ChainState→ℝ:=
  ![-p,-1-p/2,if p ≤ 1 then -3/2-p/4 else -7/4,-3/2,-1,0,2,0]
def bestPolicyHalf (p : ℝ) (s : ChainState) : ChainAction:=
  if s=2 ∧ p ≤ 1 then 0 else walkPolicy s

theorem actual_physical_cliff_is_absorbing_and_penalty_is_only_once (a : ChainAction) :
    physicalCell 0=0 ∧ physicalCell 7=0 ∧
    chainNext 0 a=7 ∧ chainNext 7 a=7 ∧
    (∀ p : ℝ,chainReward p 0 a= -p ∧ chainReward p 7 a=0) := by
  fin_cases a <;> norm_num [physicalCell,chainNext,chainReward,chainBaseReward]

theorem actual_chain_walk_and_jump_transitions :
    chainNext 2 1=3 ∧ chainNext 3 1=4 ∧ chainNext 4 1=5 ∧ chainNext 5 1=6 ∧ chainNext 6 2=6 ∧
    chainNext 2 0=1 ∧ (∀ a,chainNext 1 a=0) ∧
    chainTrajectory 2 leftPolicy 2=0 ∧ chainTrajectory 2 leftPolicy 3=7 := by
  refine ⟨by norm_num [chainNext],by norm_num [chainNext],by norm_num [chainNext],
    by norm_num [chainNext],by norm_num [chainNext],by norm_num [chainNext],?_,
    by norm_num [chainTrajectory,leftPolicy,chainNext],by norm_num [chainTrajectory,leftPolicy,chainNext]⟩
  intro a;fin_cases a <;> norm_num [chainNext]

theorem actual_walk_policy_is_allowed_and_preserves_the_kernel (s : ChainState) :
    chainAllowed s (walkPolicy s) ∧ (chainViable s→chainViable (chainNext s (walkPolicy s))) := by
  fin_cases s <;> norm_num [walkPolicy,chainAllowed,chainViable,chainNext]

theorem actual_walk_is_viable_at_every_time (initial : ChainState) (hi : chainViable initial) :
    ∀ n,chainViable (chainTrajectory initial walkPolicy n) := by
  intro n;induction n with
  |zero=>exact hi
  |succ n ih=>exact (actual_walk_policy_is_allowed_and_preserves_the_kernel _).2 ih

theorem actual_walk_half_bellman_equality (p : ℝ) (s : ChainState) :
    chainReward p s (walkPolicy s)+(1/2)*safeHalf p (chainNext s (walkPolicy s))=safeHalf p s := by
  fin_cases s <;> norm_num [chainReward,chainBaseReward,chainNext,walkPolicy,safeHalf]
  ring

theorem actual_safe_half_action_upper_bound (p : ℝ) (s : ChainState) (a : ChainAction)
    (hs : chainViable s) (hn : chainViable (chainNext s a)) (ha : chainAllowed s a) :
    chainReward p s a+(1/2)*safeHalf p (chainNext s a)  ≤  safeHalf p s := by
  fin_cases s <;> fin_cases a <;>
    simp_all [chainViable,chainNext,chainAllowed,chainReward,chainBaseReward,safeHalf] <;> norm_num

theorem actual_walk_half_attains_its_genuine_infinite_return (p : ℝ) (initial : ChainState) :
    actualReturn (1/2) (chainReward p) (chainTrajectory initial walkPolicy)
      (fun n=>walkPolicy (chainTrajectory initial walkPolicy n))=safeHalf p initial := by
  exact actual_every_bellman_equality_path_attains_the_infinite_return (1/2) (by norm_num) (by norm_num)
    chainNext (chainReward p) (safeHalf p) (chainTrajectory initial walkPolicy)
    (fun n=>walkPolicy (chainTrajectory initial walkPolicy n)) (fun _=>rfl)
    (fun n=>actual_walk_half_bellman_equality p _)

theorem actual_walk_half_is_the_attained_best_safe_history (p : ℝ) (initial : ChainState)
    (hi : chainViable initial) :
    IsGreatest {v : ℝ | ∃ state : ℕ→ChainState,∃ action : ℕ→ChainAction,
      state 0=initial ∧ (∀ n,chainViable (state n)) ∧
      (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) ∧
      actualReturn (1/2) (chainReward p) state action=v} (safeHalf p initial) := by
  refine ⟨?_,?_⟩
  · exact ⟨chainTrajectory initial walkPolicy,fun n=>walkPolicy (chainTrajectory initial walkPolicy n),
      rfl,actual_walk_is_viable_at_every_time initial hi,
      fun n=>⟨(actual_walk_policy_is_allowed_and_preserves_the_kernel _).1,rfl⟩,
      actual_walk_half_attains_its_genuine_infinite_return p initial⟩
  · rintro v ⟨state,action,h0,hviable,hpath,rfl⟩
    have h:=actual_bellman_upper_bound_bounds_every_history_dependent_return (1/2) (by norm_num) (by norm_num)
      chainNext (fun s a=>chainViable s ∧ chainViable (chainNext s a) ∧ chainAllowed s a)
      (chainReward p) (safeHalf p) (fun s a h=>actual_safe_half_action_upper_bound p s a h.1 h.2.1 h.2.2)
      state action (fun n=>⟨⟨hviable n,by rw [←(hpath n).2];exact hviable (n+1),(hpath n).1⟩,(hpath n).2⟩)
    simpa only [h0] using h

theorem actual_left_policy_half_infinite_return (p : ℝ) (initial : ChainState) :
    actualReturn (1/2) (chainReward p) (chainTrajectory initial leftPolicy)
      (fun n=>leftPolicy (chainTrajectory initial leftPolicy n))=leftHalf p initial := by
  exact actual_every_bellman_equality_path_attains_the_infinite_return (1/2) (by norm_num) (by norm_num)
    chainNext (chainReward p) (leftHalf p) (chainTrajectory initial leftPolicy)
    (fun n=>leftPolicy (chainTrajectory initial leftPolicy n)) (fun _=>rfl)
    (fun n=>by
      generalize chainTrajectory initial leftPolicy n=s
      fin_cases s <;> norm_num [chainReward,chainBaseReward,chainNext,leftPolicy,leftHalf] <;> ring)

theorem actual_best_half_policy_is_allowed (p : ℝ) (s : ChainState) :
    chainAllowed s (bestPolicyHalf p s) := by
  by_cases hp : p ≤ 1 <;> fin_cases s <;> norm_num [bestPolicyHalf,walkPolicy,chainAllowed,hp]

theorem actual_best_half_bellman_equality (p : ℝ) (s : ChainState) :
    chainReward p s (bestPolicyHalf p s)+(1/2)*bestHalf p (chainNext s (bestPolicyHalf p s))=bestHalf p s := by
  by_cases hp : p ≤ 1 <;> fin_cases s <;>
    norm_num [bestPolicyHalf,walkPolicy,chainNext,chainReward,chainBaseReward,bestHalf,hp] <;> ring

theorem actual_best_half_bellman_global_upper (p : ℝ) (hp0 : 0 ≤ p) (s : ChainState) (a : ChainAction)
    (ha : chainAllowed s a) : chainReward p s a+(1/2)*bestHalf p (chainNext s a)  ≤  bestHalf p s := by
  by_cases hp : p ≤ 1 <;> fin_cases s <;> fin_cases a <;>
    simp_all [chainNext,chainAllowed,chainReward,chainBaseReward,bestHalf] <;> (try split_ifs at *) <;> norm_num at * <;> linarith

theorem actual_best_half_policy_attains_its_genuine_infinite_return (p : ℝ) (initial : ChainState) :
    actualReturn (1/2) (chainReward p) (chainTrajectory initial (bestPolicyHalf p))
      (fun n=>bestPolicyHalf p (chainTrajectory initial (bestPolicyHalf p) n))=bestHalf p initial := by
  exact actual_every_bellman_equality_path_attains_the_infinite_return (1/2) (by norm_num) (by norm_num)
    chainNext (chainReward p) (bestHalf p) (chainTrajectory initial (bestPolicyHalf p))
    (fun n=>bestPolicyHalf p (chainTrajectory initial (bestPolicyHalf p) n)) (fun _=>rfl)
    (fun n=>actual_best_half_bellman_equality p _)

theorem actual_best_half_is_the_attained_optimum_over_every_history (p : ℝ) (hp0 : 0 ≤ p)
    (initial : ChainState) :
    IsGreatest {v : ℝ | ∃ state : ℕ→ChainState,∃ action : ℕ→ChainAction,
      state 0=initial ∧
      (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) ∧
      actualReturn (1/2) (chainReward p) state action=v} (bestHalf p initial) := by
  refine ⟨?_,?_⟩
  · exact ⟨chainTrajectory initial (bestPolicyHalf p),fun n=>bestPolicyHalf p (chainTrajectory initial (bestPolicyHalf p) n),
      rfl,fun n=>⟨actual_best_half_policy_is_allowed p _,rfl⟩,actual_best_half_policy_attains_its_genuine_infinite_return p initial⟩
  · rintro v ⟨state,action,h0,hpath,rfl⟩
    have h:=actual_bellman_upper_bound_bounds_every_history_dependent_return (1/2) (by norm_num) (by norm_num)
      chainNext chainAllowed (chainReward p) (bestHalf p) (actual_best_half_bellman_global_upper p hp0) state action hpath
    simpa only [h0] using h

theorem actual_half_jump_comparison_and_no_other_tempted_viable_state (p : ℝ) (hp0 : 0 ≤ p) :
    safeHalf p 2= -7/4 ∧ leftHalf p 2= -3/2-p/4 ∧
    (leftHalf p 2>safeHalf p 2 ↔ p<1) ∧
    (leftHalf p 2=safeHalf p 2 ↔ p=1) ∧
    leftHalf p 3= -7/4-p/8 ∧ leftHalf p 3<safeHalf p 3 := by
  norm_num [safeHalf,leftHalf]
  constructor
  · constructor <;> intro h <;> linarith
  · constructor
    · constructor <;> intro h <;> linarith
    · linarith


-- An optimal history has an optimal true suffix; no Markov-policy assumption is used.
theorem actual_optimal_history_has_an_optimal_true_tail
    {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (next : S → A → S)
    (allowed : S → A → Prop) (reward : S → A → ℝ) (value : S → ℝ)
    (hbellman : ∀ s a, allowed s a → reward s a + γ * value (next s a) ≤ value s)
    (state : ℕ → S) (action : ℕ → A)
    (hpath : ∀ n, allowed (state n) (action n) ∧ state (n + 1) = next (state n) (action n))
    (hopt : actualReturn γ reward state action = value (state 0)) :
    actualReturn γ reward (fun n => state (n + 1)) (fun n => action (n + 1)) = value (state 1) := by
  have hu := actual_bellman_upper_bound_bounds_every_history_dependent_return γ hγ0.le hγ1
    next allowed reward value hbellman (fun n => state (n + 1)) (fun n => action (n + 1))
    (fun n => by simpa only [Nat.add_assoc] using hpath (n + 1))
  have hf := actual_infinite_return_keeps_the_first_action_and_true_tail γ hγ0.le hγ1 reward state action
  have hb := hbellman (state 0) (action 0) (hpath 0).1
  rw [← (hpath 0).2] at hb
  apply le_antisymm hu
  by_contra h
  have hl : actualReturn γ reward (fun n => state (n + 1)) (fun n => action (n + 1)) < value (state 1) := lt_of_not_ge h
  have hm := mul_lt_mul_of_pos_left hl hγ0
  rw [hopt] at hf
  linarith

theorem actual_only_exit_from_the_viable_chain (s : ChainState) (a : ChainAction)
    (hs : chainViable s) (ha : chainAllowed s a) :
    ¬chainViable (chainNext s a) ↔ s = 2 ∧ a = 0 := by
  fin_cases s <;> fin_cases a <;> norm_num [chainViable,chainAllowed,chainNext] at *

def PenaltySafeHalf (p : ℝ) : Prop :=
  ∀ state : ℕ → ChainState, ∀ action : ℕ → ChainAction,
    chainViable (state 0) →
    (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) →
    actualReturn (1/2) (chainReward p) state action=bestHalf p (state 0) →
    ∀ n,chainViable (state n)

theorem actual_half_optimal_history_cannot_take_the_unsafe_exit (p : ℝ) (hp : 1 < p)
    (state : ℕ → ChainState) (action : ℕ → ChainAction)
    (hs : chainViable (state 0))
    (hpath : ∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n))
    (hopt : actualReturn (1/2) (chainReward p) state action=bestHalf p (state 0)) :
    chainViable (state 1) := by
  by_contra hn
  have hexit := (actual_only_exit_from_the_viable_chain (state 0) (action 0) hs (hpath 0).1).1
    (by simpa only [←(hpath 0).2] using hn)
  have hu := actual_bellman_upper_bound_bounds_every_history_dependent_return (1/2) (by norm_num) (by norm_num)
    chainNext chainAllowed (chainReward p) (bestHalf p)
    (actual_best_half_bellman_global_upper p (by linarith))
    (fun n => state (n+1)) (fun n => action (n+1))
    (fun n => by simpa only [Nat.add_assoc] using hpath (n+1))
  have hf := actual_infinite_return_keeps_the_first_action_and_true_tail (1/2) (by norm_num) (by norm_num)
    (chainReward p) state action
  have h1 : state 1 = 1 := by simpa [hexit.1,hexit.2,chainNext] using (hpath 0).2
  rw [hopt] at hf
  simp [hexit.1,h1,chainReward,chainBaseReward,bestHalf,not_le_of_gt hp] at hf hu
  linarith

theorem actual_every_half_optimal_history_is_safe_above_one (p : ℝ) (hp : 1 < p) :
    PenaltySafeHalf p := by
  intro state action h0 hpath hopt n
  have hpair : ∀ k,
      chainViable (state k) ∧
      actualReturn (1/2) (chainReward p) (fun m => state (m+k)) (fun m => action (m+k)) = bestHalf p (state k) := by
    intro k
    induction k with
    | zero => simpa using And.intro h0 hopt
    | succ k ih =>
      have ht := actual_optimal_history_has_an_optimal_true_tail (1/2) (by norm_num) (by norm_num)
        chainNext chainAllowed (chainReward p) (bestHalf p) (actual_best_half_bellman_global_upper p (by linarith))
        (fun m => state (m+k)) (fun m => action (m+k))
        (fun m => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpath (m+k)) (by simpa using ih.2)
      have hv := actual_half_optimal_history_cannot_take_the_unsafe_exit p hp
        (fun m => state (m+k)) (fun m => action (m+k)) (by simpa using ih.1)
        (fun m => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpath (m+k)) (by simpa using ih.2)
      exact ⟨by simpa [Nat.add_comm] using hv,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht⟩
  exact (hpair n).1

theorem actual_half_penalty_one_is_a_true_infimum_but_is_not_safe (p : ℝ) (_hp0 : 0 ≤ p) :
    PenaltySafeHalf p ↔ 1 < p := by
  constructor
  · intro hsafe
    by_contra h
    have hp : p ≤ 1 := le_of_not_gt h
    have hb := hsafe (chainTrajectory 2 (bestPolicyHalf p))
      (fun n => bestPolicyHalf p (chainTrajectory 2 (bestPolicyHalf p) n))
      (by norm_num [chainTrajectory,chainViable])
      (fun n => ⟨actual_best_half_policy_is_allowed p _,rfl⟩)
      (actual_best_half_policy_attains_its_genuine_infinite_return p 2) 1
    norm_num [chainTrajectory,bestPolicyHalf,hp,chainNext,chainViable] at hb
  · exact actual_every_half_optimal_history_is_safe_above_one p

theorem actual_half_safe_penalties_have_infimum_one_not_attained :
    IsGLB {p : ℝ | 0 ≤ p ∧ PenaltySafeHalf p} 1 ∧ ¬PenaltySafeHalf 1 := by
  have he : {p : ℝ | 0 ≤ p ∧ PenaltySafeHalf p} = Ioi 1 := by
    ext p
    constructor
    · rintro ⟨hp,hs⟩
      exact (actual_half_penalty_one_is_a_true_infimum_but_is_not_safe p hp).1 hs
    · intro hp
      change 1 < p at hp
      exact ⟨by linarith,actual_every_half_optimal_history_is_safe_above_one p hp⟩
  rw [he]
  exact ⟨(isGLB_Ioi : IsGLB (Ioi (1 : ℝ)) 1),by
    intro h
    have := (actual_half_penalty_one_is_a_true_infimum_but_is_not_safe 1 (by norm_num)).1 h
    linarith⟩

-- These extrema use the original seven physical cells, including the zero-reward cliff.
def originalChainState (s : ChainState) : Prop := s.val ≤ 6

theorem actual_chain_reward_extrema_and_failure_horizon :
    IsGreatest {r : ℝ | ∃ s : ChainState, originalChainState s ∧ ¬chainViable s ∧ chainBaseReward s=r} 0 ∧
    IsGreatest {r : ℝ | ∃ s : ChainState,∃ a : ChainAction, originalChainState s ∧ chainAllowed s a ∧
      ¬chainViable (chainNext s a) ∧ chainBaseReward s=r} 0 ∧
    IsLeast {r : ℝ | ∃ s : ChainState,∃ a : ChainAction, chainViable s ∧ chainAllowed s a ∧
      chainViable (chainNext s a) ∧ chainBaseReward s=r} (-1) ∧
    (∀ s : ChainState, originalChainState s → ¬chainViable s →
      s=0 ∨ ∀ a : ChainAction,physicalCell (chainNext s a)=0) := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨⟨0,by norm_num [originalChainState],by norm_num [chainViable],by norm_num [chainBaseReward]⟩,?_⟩
    rintro r ⟨s,hs,hn,rfl⟩
    fin_cases s <;> norm_num [originalChainState,chainViable,chainBaseReward] at *
  · refine ⟨⟨0,0,by norm_num [originalChainState],by norm_num [chainAllowed],by norm_num [chainViable,chainNext],by norm_num [chainBaseReward]⟩,?_⟩
    rintro r ⟨s,a,hs,ha,hn,rfl⟩
    fin_cases s <;> fin_cases a <;> norm_num [originalChainState,chainBaseReward,chainAllowed,chainNext,chainViable] at *
  · refine ⟨⟨2,1,by norm_num [chainViable],by norm_num [chainAllowed],by norm_num [chainViable,chainNext],by norm_num [chainBaseReward]⟩,?_⟩
    rintro r ⟨s,a,hs,ha,hn,rfl⟩
    fin_cases s <;> norm_num [chainViable,chainBaseReward] at *
  · intro s hs hn
    fin_cases s <;> norm_num [originalChainState,chainViable] at *
    intro a
    fin_cases a <;> norm_num [physicalCell,chainNext]

theorem actual_half_safe_value_has_attained_infimum (p : ℝ) :
    IsLeast {v : ℝ | ∃ s : ChainState,chainViable s ∧ safeHalf p s=v} (-7/4) := by
  refine ⟨⟨2,by norm_num [chainViable],by norm_num [safeHalf]⟩,?_⟩
  rintro v ⟨s,hs,rfl⟩
  fin_cases s <;> norm_num [chainViable,safeHalf] at *

theorem actual_half_unsafe_values_have_the_true_attained_supremum (p : ℝ) :
    IsGreatest {v : ℝ | ∃ s : ChainState, originalChainState s ∧ ¬chainViable s ∧ bestHalf p s=v}
      (max (-p) (-1-p/2)) := by
  refine ⟨?_,?_⟩
  · by_cases h : -p ≤ -1-p/2
    · exact ⟨1,by norm_num [originalChainState],by norm_num [chainViable],by simp [bestHalf,max_eq_right h]⟩
    · exact ⟨0,by norm_num [originalChainState],by norm_num [chainViable],by simp [bestHalf,max_eq_left (le_of_not_ge h)]⟩
  · rintro v ⟨s,hs,hn,rfl⟩
    fin_cases s <;> norm_num [originalChainState,chainViable,bestHalf] at *

def strictZeroingBoundHalf (p : ℝ) : Prop :=
  (1/2)*max (-p) (-1-p/2) < -1+(1/2)*(-7/4)

theorem actual_theorem_two_half_threshold_and_true_zeroing_intermediate (p : ℝ) :
    ((1/2 : ℝ)^(-1 : ℤ)*(0*(1-(1/2)^2)/(1-1/2)+(0-(-1))/(1/2)-(-7/4))) = 15/2 ∧
    (strictZeroingBoundHalf p ↔ 11/2 < p) ∧
    ((15/2 : ℝ)/1 = 15/2) := by
  norm_num
  unfold strictZeroingBoundHalf
  constructor
  · intro h
    have hl := le_max_left (-p) (-1-p/2)
    have hr := le_max_right (-p) (-1-p/2)
    linarith
  · intro h
    have hm : max (-p) (-1-p/2) < -15/4 := (max_lt_iff).2 ⟨by linarith,by linarith⟩
    linarith

theorem actual_zeroing_intermediate_infimum_is_not_attained :
    IsGLB {p : ℝ | 0 ≤ p ∧ strictZeroingBoundHalf p} (11/2) ∧ ¬strictZeroingBoundHalf (11/2) := by
  have hi (p : ℝ) := (actual_theorem_two_half_threshold_and_true_zeroing_intermediate p).2.1
  have he : {p : ℝ | 0 ≤ p ∧ strictZeroingBoundHalf p} = Ioi (11/2) := by
    ext p
    constructor
    · rintro ⟨hp,hs⟩
      exact (hi p).1 hs
    · intro hp
      change 11/2 < p at hp
      exact ⟨by linarith,(hi p).2 hp⟩
  rw [he]
  exact ⟨(isGLB_Ioi : IsGLB (Ioi (11/2 : ℝ)) (11/2)),by intro h;have := (hi (11/2)).1 h;linarith⟩

theorem actual_sufficient_half_bound_and_its_two_reward_slacks (p : ℝ) (hp : 15/2 < p) :
    PenaltySafeHalf p ∧
    chainBaseReward 1 = -1 ∧ chainBaseReward 2 = -1 ∧
    0-chainBaseReward 1=1 ∧ 0-chainBaseReward 2=1 := by
  refine ⟨actual_every_half_optimal_history_is_safe_above_one p (by linarith),?_⟩
  norm_num [chainBaseReward]


-- The long-horizon branch uses the same actual transition/reward model.
def safeNine (p : ℝ) : ChainState → ℝ := ![-p,-1-(9/10)*p,1561/500,229/50,31/5,8,10,0]
def leftNine (p : ℝ) : ChainState → ℝ :=
  ![-p,-1-(9/10)*p,-19/10-(81/100)*p,-271/100-(729/1000)*p,
    -3439/1000-(6561/10000)*p,-40951/10000-(59049/100000)*p,
    -268559/100000-(531441/1000000)*p,0]

theorem actual_walk_nine_bellman_equality (p : ℝ) (s : ChainState) :
    chainReward p s (walkPolicy s)+(9/10)*safeNine p (chainNext s (walkPolicy s))=safeNine p s := by
  fin_cases s <;> norm_num [chainReward,chainBaseReward,chainNext,walkPolicy,safeNine]
  ring

theorem actual_nine_bellman_global_upper (p : ℝ) (hp0 : 0 ≤ p) (s : ChainState) (a : ChainAction)
    (ha : chainAllowed s a) : chainReward p s a+(9/10)*safeNine p (chainNext s a) ≤ safeNine p s := by
  fin_cases s <;> fin_cases a <;>
    simp_all [chainNext,chainAllowed,chainReward,chainBaseReward,safeNine] <;> norm_num at * <;> linarith

theorem actual_walk_nine_attains_its_genuine_infinite_return (p : ℝ) (initial : ChainState) :
    actualReturn (9/10) (chainReward p) (chainTrajectory initial walkPolicy)
      (fun n=>walkPolicy (chainTrajectory initial walkPolicy n))=safeNine p initial := by
  exact actual_every_bellman_equality_path_attains_the_infinite_return (9/10) (by norm_num) (by norm_num)
    chainNext (chainReward p) (safeNine p) (chainTrajectory initial walkPolicy)
    (fun n=>walkPolicy (chainTrajectory initial walkPolicy n)) (fun _=>rfl)
    (fun n=>actual_walk_nine_bellman_equality p _)

theorem actual_walk_nine_is_the_attained_optimum_over_every_history (p : ℝ) (hp0 : 0 ≤ p)
    (initial : ChainState) :
    IsGreatest {v : ℝ | ∃ state : ℕ→ChainState,∃ action : ℕ→ChainAction,
      state 0=initial ∧
      (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) ∧
      actualReturn (9/10) (chainReward p) state action=v} (safeNine p initial) := by
  refine ⟨?_,?_⟩
  · exact ⟨chainTrajectory initial walkPolicy,fun n=>walkPolicy (chainTrajectory initial walkPolicy n),
      rfl,fun n=>⟨(actual_walk_policy_is_allowed_and_preserves_the_kernel _).1,rfl⟩,
      actual_walk_nine_attains_its_genuine_infinite_return p initial⟩
  · rintro v ⟨state,action,h0,hpath,rfl⟩
    have h:=actual_bellman_upper_bound_bounds_every_history_dependent_return (9/10) (by norm_num) (by norm_num)
      chainNext chainAllowed (chainReward p) (safeNine p) (actual_nine_bellman_global_upper p hp0) state action hpath
    simpa only [h0] using h

theorem actual_walk_nine_is_the_attained_best_safe_history (p : ℝ) (initial : ChainState)
    (hi : chainViable initial) :
    IsGreatest {v : ℝ | ∃ state : ℕ→ChainState,∃ action : ℕ→ChainAction,
      state 0=initial ∧ (∀ n,chainViable (state n)) ∧
      (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) ∧
      actualReturn (9/10) (chainReward p) state action=v} (safeNine p initial) := by
  have hu (s : ChainState) (a : ChainAction) (hs : chainViable s)
      (hn : chainViable (chainNext s a)) (ha : chainAllowed s a) :
      chainReward p s a+(9/10)*safeNine p (chainNext s a) ≤ safeNine p s := by
    fin_cases s <;> fin_cases a <;> norm_num [chainViable,chainAllowed,chainNext,chainReward,chainBaseReward,safeNine] at *
  refine ⟨?_,?_⟩
  · exact ⟨chainTrajectory initial walkPolicy,fun n=>walkPolicy (chainTrajectory initial walkPolicy n),
      rfl,actual_walk_is_viable_at_every_time initial hi,
      fun n=>⟨(actual_walk_policy_is_allowed_and_preserves_the_kernel _).1,rfl⟩,
      actual_walk_nine_attains_its_genuine_infinite_return p initial⟩
  · rintro v ⟨state,action,h0,hviable,hpath,rfl⟩
    have h:=actual_bellman_upper_bound_bounds_every_history_dependent_return (9/10) (by norm_num) (by norm_num)
      chainNext (fun s a=>chainViable s ∧ chainViable (chainNext s a) ∧ chainAllowed s a)
      (chainReward p) (safeNine p) (fun s a h=>hu s a h.1 h.2.1 h.2.2)
      state action (fun n=>⟨⟨hviable n,by rw [←(hpath n).2];exact hviable (n+1),(hpath n).1⟩,(hpath n).2⟩)
    simpa only [h0] using h

theorem actual_left_policy_nine_infinite_return (p : ℝ) (initial : ChainState) :
    actualReturn (9/10) (chainReward p) (chainTrajectory initial leftPolicy)
      (fun n=>leftPolicy (chainTrajectory initial leftPolicy n))=leftNine p initial := by
  exact actual_every_bellman_equality_path_attains_the_infinite_return (9/10) (by norm_num) (by norm_num)
    chainNext (chainReward p) (leftNine p) (chainTrajectory initial leftPolicy)
    (fun n=>leftPolicy (chainTrajectory initial leftPolicy n)) (fun _=>rfl)
    (fun n=>by
      generalize chainTrajectory initial leftPolicy n=s
      fin_cases s <;> norm_num [chainReward,chainBaseReward,chainNext,leftPolicy,leftNine] <;> ring)

def PenaltySafeNine (p : ℝ) : Prop :=
  ∀ state : ℕ → ChainState, ∀ action : ℕ → ChainAction,
    chainViable (state 0) →
    (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) →
    actualReturn (9/10) (chainReward p) state action=safeNine p (state 0) →
    ∀ n,chainViable (state n)

theorem actual_nine_optimal_history_cannot_take_the_unsafe_exit (p : ℝ) (hp : 0 ≤ p)
    (state : ℕ → ChainState) (action : ℕ → ChainAction)
    (hs : chainViable (state 0))
    (hpath : ∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n))
    (hopt : actualReturn (9/10) (chainReward p) state action=safeNine p (state 0)) :
    chainViable (state 1) := by
  by_contra hn
  have hexit := (actual_only_exit_from_the_viable_chain (state 0) (action 0) hs (hpath 0).1).1
    (by simpa only [←(hpath 0).2] using hn)
  have hu := actual_bellman_upper_bound_bounds_every_history_dependent_return (9/10) (by norm_num) (by norm_num)
    chainNext chainAllowed (chainReward p) (safeNine p) (actual_nine_bellman_global_upper p hp)
    (fun n => state (n+1)) (fun n => action (n+1))
    (fun n => by simpa only [Nat.add_assoc] using hpath (n+1))
  have hf := actual_infinite_return_keeps_the_first_action_and_true_tail (9/10) (by norm_num) (by norm_num)
    (chainReward p) state action
  have h1 : state 1 = 1 := by simpa [hexit.1,hexit.2,chainNext] using (hpath 0).2
  rw [hopt] at hf
  simp [hexit.1,h1,chainReward,chainBaseReward,safeNine] at hf hu
  linarith

theorem actual_every_nine_optimal_history_is_safe_with_zero_penalty (p : ℝ) (hp : 0 ≤ p) :
    PenaltySafeNine p := by
  intro state action h0 hpath hopt n
  have hpair : ∀ k,
      chainViable (state k) ∧
      actualReturn (9/10) (chainReward p) (fun m => state (m+k)) (fun m => action (m+k)) = safeNine p (state k) := by
    intro k
    induction k with
    | zero => simpa using And.intro h0 hopt
    | succ k ih =>
      have ht := actual_optimal_history_has_an_optimal_true_tail (9/10) (by norm_num) (by norm_num)
        chainNext chainAllowed (chainReward p) (safeNine p) (actual_nine_bellman_global_upper p hp)
        (fun m => state (m+k)) (fun m => action (m+k))
        (fun m => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpath (m+k)) (by simpa using ih.2)
      have hv := actual_nine_optimal_history_cannot_take_the_unsafe_exit p hp
        (fun m => state (m+k)) (fun m => action (m+k)) (by simpa using ih.1)
        (fun m => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpath (m+k)) (by simpa using ih.2)
      exact ⟨by simpa [Nat.add_comm] using hv,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht⟩
  exact (hpair n).1

theorem actual_nine_zero_is_an_attained_minimum_safe_penalty :
    IsLeast {p : ℝ | 0 ≤ p ∧ PenaltySafeNine p} 0 := by
  exact ⟨⟨le_rfl,actual_every_nine_optimal_history_is_safe_with_zero_penalty 0 le_rfl⟩,fun p hp=>hp.1⟩

theorem actual_nine_safe_value_has_attained_infimum (p : ℝ) :
    IsLeast {v : ℝ | ∃ s : ChainState,chainViable s ∧ safeNine p s=v} (1561/500) := by
  refine ⟨⟨2,by norm_num [chainViable],by norm_num [safeNine]⟩,?_⟩
  rintro v ⟨s,hs,rfl⟩
  fin_cases s <;> norm_num [chainViable,safeNine] at *

theorem actual_both_geometric_walk_formulas_and_nine_strictly_losing_jump (p : ℝ) (hp : 0 ≤ p) :
    safeHalf p 2= -(1+(1/2)+(1/2)^2+(1/2)^3)+(1/2)^4/(1-1/2) ∧
    safeNine p 2= -(1+(9/10)+(9/10)^2+(9/10)^3)+(9/10)^4/(1-9/10) ∧
    safeNine p 2=1561/500 ∧ leftNine p 2= -19/10-(81/100)*p ∧ leftNine p 2<0 := by
  norm_num [safeHalf,safeNine,leftNine]
  linarith

theorem actual_nine_theorem_two_threshold_is_negative_and_rounds_to_minus_two_point_two :
    ((9/10 : ℝ)^(-1 : ℤ)*(0*(1-(9/10)^2)/(1-9/10)+(0-(-1))/(9/10)-(1561/500))) = -9049/4050 ∧
    -225/100 < (-9049/4050 : ℝ) ∧ (-9049/4050 : ℝ) < -215/100 ∧ (-9049/4050 : ℝ)<0 := by
  norm_num


-- The jumping return is an actual admissible history, not just a scalar comparator.
theorem actual_jump_from_two_is_admissible_and_reaches_the_cliff :
    (∀ n,chainAllowed (chainTrajectory 2 leftPolicy n) (leftPolicy (chainTrajectory 2 leftPolicy n))) ∧
    ¬chainViable (chainTrajectory 2 leftPolicy 1) ∧
    physicalCell (chainTrajectory 2 leftPolicy 2)=0 := by
  have hm : ∀ n,chainTrajectory 2 leftPolicy n ∈ ({0,1,2,7} : Set ChainState) := by
    intro n
    induction n with
    | zero => norm_num [chainTrajectory]
    | succ n ih =>
      change chainNext (chainTrajectory 2 leftPolicy n) 0 ∈ ({0,1,2,7} : Set ChainState)
      generalize chainTrajectory 2 leftPolicy n=s at ih ⊢
      fin_cases s <;> norm_num [chainNext] at *
  refine ⟨?_,by norm_num [chainTrajectory,leftPolicy,chainNext,chainViable],
    by norm_num [chainTrajectory,leftPolicy,chainNext,physicalCell]⟩
  intro n
  have h:=hm n
  generalize chainTrajectory 2 leftPolicy n=s at h ⊢
  fin_cases s <;> norm_num [chainAllowed,leftPolicy] at *

theorem actual_jumping_from_two_is_half_optimal_exactly_below_or_at_one
    (p : ℝ) (hp0 : 0 ≤ p) :
    IsGreatest {v : ℝ | ∃ state : ℕ→ChainState,∃ action : ℕ→ChainAction,
      state 0=2 ∧
      (∀ n,chainAllowed (state n) (action n) ∧ state (n+1)=chainNext (state n) (action n)) ∧
      actualReturn (1/2) (chainReward p) state action=v} (leftHalf p 2) ↔ p ≤ 1 := by
  have hg:=actual_best_half_is_the_attained_optimum_over_every_history p hp0 2
  constructor
  · intro hj
    have he:=hj.unique hg
    by_contra hn
    have hp : 1 < p := lt_of_not_ge hn
    norm_num [bestHalf,leftHalf,not_le_of_gt hp] at he
    linarith
  · intro hp
    simpa [bestHalf,leftHalf,hp] using hg

theorem actual_at_the_half_threshold_safe_and_unsafe_histories_both_attain_the_global_maximum :
    actualReturn (1/2) (chainReward 1) (chainTrajectory 2 walkPolicy)
      (fun n=>walkPolicy (chainTrajectory 2 walkPolicy n)) = -7/4 ∧
    actualReturn (1/2) (chainReward 1) (chainTrajectory 2 leftPolicy)
      (fun n=>leftPolicy (chainTrajectory 2 leftPolicy n)) = -7/4 ∧
    (∀ n,chainViable (chainTrajectory 2 walkPolicy n)) ∧
    ¬chainViable (chainTrajectory 2 leftPolicy 1) := by
  refine ⟨?_,?_,actual_walk_is_viable_at_every_time 2 (by norm_num [chainViable]),
    actual_jump_from_two_is_admissible_and_reaches_the_cliff.2.1⟩
  · rw [actual_walk_half_attains_its_genuine_infinite_return]
    norm_num [safeHalf]
  · rw [actual_left_policy_half_infinite_return]
    norm_num [leftHalf]

theorem actual_slope_has_exactly_one_step_until_physical_failure :
    physicalCell 1≠0 ∧ (∀ a : ChainAction,physicalCell (chainNext 1 a)=0) ∧
    physicalCell 0=0 ∧ (∀ a : ChainAction,physicalCell (chainNext 0 a)=0) := by
  refine ⟨by norm_num [physicalCell],?_,by norm_num [physicalCell],?_⟩ <;>
    intro a <;> fin_cases a <;> norm_num [physicalCell,chainNext]

theorem actual_corrected_long_horizon_value_rounds_to_the_original_two_decimal_target :
    (623/200 : ℝ) < 1561/500 ∧ (1561/500 : ℝ)<625/200 ∧
    (1561/500 : ℝ)≠(78/25 : ℝ) ∧
    (-(3439/1000 : ℝ)+6561/1000)=1561/500 := by
  norm_num

end SafeLearning.CompleteModulesChainPenaltyWhole30

namespace SafeLearning.CompleteModulesChainPenaltyWhole30
open MeasureTheory
local instance : MeasurableSpace ChainState := ⊤

def actualChainHistoryValues (p : ℝ) (initial : ChainState) : Set ℝ :=
  {v | ∃ state : ℕ → ChainState, ∃ action : ℕ → ChainAction,
    state 0 = initial ∧
    (∀ n, chainAllowed (state n) (action n) ∧ state (n + 1) = chainNext (state n) (action n)) ∧
    actualReturn (1/2) (chainReward p) state action = v}

def actualChainPointwiseValue (p : ℝ) (initial : ChainState) : ℝ :=
  sSup (actualChainHistoryValues p initial)

def actualChainDualDirac (p : ℝ) : ℝ :=
  ∫ initial, actualChainPointwiseValue p initial ∂Measure.dirac (2 : ChainState)

def actualChainSafePrimalAtTwo : ℝ :=
  sSup {v | ∃ state : ℕ → ChainState, ∃ action : ℕ → ChainAction,
    state 0 = (2 : ChainState) ∧ (∀ n, chainViable (state n)) ∧
    (∀ n, chainAllowed (state n) (action n) ∧ state (n + 1) = chainNext (state n) (action n)) ∧
    actualReturn (1/2) (chainReward 0) state action = v}

theorem actual_chain_history_supremum_is_its_genuine_attained_Bellman_value
    (p : ℝ) (hp : 0 ≤ p) (initial : ChainState) :
    actualChainPointwiseValue p initial = bestHalf p initial :=
  (actual_best_half_is_the_attained_optimum_over_every_history p hp initial).csSup_eq

theorem actual_delta_two_expected_chain_dual_has_the_printed_max_profile
    (p : ℝ) (hp : 0 ≤ p) :
    actualChainDualDirac p = max (-7/4) (-3/2 - p/4) := by
  rw [actualChainDualDirac, integral_dirac,
    actual_chain_history_supremum_is_its_genuine_attained_Bellman_value p hp]
  by_cases h : p ≤ 1
  · rw [max_eq_right (by linarith)]
    simp [bestHalf, h]
  · rw [max_eq_left (by linarith [lt_of_not_ge h])]
    simp [bestHalf, h]

theorem actual_delta_two_safe_primal_has_the_attained_printed_value :
    actualChainSafePrimalAtTwo = -7/4 := by
  have h := (actual_walk_half_is_the_attained_best_safe_history 0 2
    (by norm_num [chainViable])).csSup_eq
  simpa [actualChainSafePrimalAtTwo, safeHalf] using h

theorem actual_delta_two_chain_dual_optimal_set_is_the_printed_closed_ray :
    {p : ℝ | 0 ≤ p ∧ actualChainDualDirac p = actualChainSafePrimalAtTwo} = Ici (1 : ℝ) := by
  ext p
  rw [actual_delta_two_safe_primal_has_the_attained_printed_value]
  constructor
  · rintro ⟨hp, h⟩
    rw [actual_delta_two_expected_chain_dual_has_the_printed_max_profile p hp] at h
    have hl := le_max_right (-7/4 : ℝ) (-3/2 - p/4)
    rw [h] at hl
    exact show 1 ≤ p by linarith
  · intro hp
    change 1 ≤ p at hp
    have hp0 : 0 ≤ p := by exact le_trans (by norm_num) hp
    refine ⟨hp0, ?_⟩
    rw [actual_delta_two_expected_chain_dual_has_the_printed_max_profile p hp0,
      max_eq_left (by linarith)]

end SafeLearning.CompleteModulesChainPenaltyWhole30
