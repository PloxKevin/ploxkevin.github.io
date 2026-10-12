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
  fin_cases s <;> norm_num [chainReward,chainBaseReward,chainNext,walkPolicy,safeHalf] <;> ring

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
    simp_all [chainNext,chainAllowed,chainReward,chainBaseReward,bestHalf,hp] <;> norm_num at * <;> linarith

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

end SafeLearning.CompleteModulesChainPenaltyWhole30
