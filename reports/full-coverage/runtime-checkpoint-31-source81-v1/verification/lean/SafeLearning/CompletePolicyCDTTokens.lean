import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompletePolicyCDTTokens
open Set
open scoped BigOperators

def datasetReward : Fin 5→ℝ := ![10,8,6,5,3]
def datasetCost : Fin 5→ℝ := ![30,15,5,12,0]
def safeDataset (budget : ℝ) : Finset (Fin 5) := Finset.univ.filter (fun i=>datasetCost i≤budget)
def datasetFrontier (budget : ℝ) : ℝ := sSup (datasetReward '' {i | datasetCost i≤budget})

theorem actual_finite_safe_argmax_and_frontier {T : Type*} [DecidableEq T]
    (data : Finset T) (reward : T→ℝ) (cost : T→ℝ) (budget : ℝ)
    (hne : (data.filter (fun t=>cost t≤budget)).Nonempty) :
    ∃ best∈data, cost best≤budget ∧
      (∀ t∈data,cost t≤budget → reward t≤reward best) ∧
      sSup (reward '' {t | t∈data ∧ cost t≤budget})=reward best := by
  classical
  obtain ⟨best,hbest,hm⟩ := Finset.exists_max_image (data.filter (fun t=>cost t≤budget)) reward hne
  have hb := Finset.mem_filter.mp hbest
  have hset : (reward '' {t | t∈data ∧ cost t≤budget}).Nonempty := ⟨reward best,⟨best,hb,rfl⟩⟩
  have hbounded : BddAbove (reward '' {t | t∈data ∧ cost t≤budget}) :=
    ((data.finite_toSet.subset (by intro t ht;exact ht.1)).image reward).bddAbove
  refine ⟨best,hb.1,hb.2,?_,?_⟩
  · intro t ht hc;exact hm t (Finset.mem_filter.mpr ⟨ht,hc⟩)
  · apply le_antisymm
    · apply csSup_le hset
      rintro value ⟨t,ht,rfl⟩
      exact hm t (Finset.mem_filter.mpr ht)
    · exact le_csSup hbounded ⟨best,hb,rfl⟩

theorem actual_budget_ten_safe_dataset : safeDataset 10={2,4} := by
  ext i
  simp only [safeDataset,Finset.mem_filter,Finset.mem_univ,true_and]
  fin_cases i <;> norm_num [datasetCost,Set.mem_ofPred_eq]

theorem actual_budget_ten_unique_best (i : Fin 5) (hi : datasetCost i≤10) :
    datasetReward i≤6 ∧ (datasetReward i=6↔i=2) := by
  fin_cases i <;> norm_num [datasetCost,datasetReward] at *

theorem actual_budget_ten_frontier : datasetFrontier 10=6 := by
  have hset : (datasetReward '' {i | datasetCost i≤10}).Nonempty :=
    ⟨6,⟨2,by norm_num [datasetCost],by norm_num [datasetReward]⟩⟩
  have hb : BddAbove (datasetReward '' {i | datasetCost i≤10}) :=
    ((Set.toFinite _).image datasetReward).bddAbove
  apply le_antisymm
  · apply csSup_le hset
    rintro value ⟨i,hi,rfl⟩
    exact (actual_budget_ten_unique_best i hi).1
  · exact le_csSup hb ⟨2,by norm_num [datasetCost],by norm_num [datasetReward]⟩

theorem actual_reward_nine_is_unsupported :
    (∀ i : Fin 5,datasetCost i≤10→datasetReward i<9) ∧
    (∀ i : Fin 5,8≤datasetReward i→10<datasetCost i) := by
  constructor
  · intro i hi;linarith [(actual_budget_ten_unique_best i hi).1]
  · intro i hi;fin_cases i <;> norm_num [datasetReward,datasetCost] at *

def nextTokens (rewardToken costToken reward cost : ℝ) : ℝ×ℝ :=
  (rewardToken-reward,costToken-cost)

theorem actual_initial_and_online_tokens :
    datasetFrontier 10=6 ∧ nextTokens 6 10 (1/2) 1=(11/2,9) := by
  exact ⟨actual_budget_ten_frontier,by norm_num [nextTokens]⟩

def remainingSum (horizon time : ℕ) (values : ℕ→ℝ) : ℝ :=
  ∑ step∈Finset.Ico time horizon,values step
def episodeTotal (horizon : ℕ) (values : ℕ→ℝ) : ℝ :=
  ∑ step∈Finset.range horizon,values step
def shiftedToken (target : ℝ) (horizon time : ℕ) (values : ℕ→ℝ) : ℝ :=
  remainingSum horizon time values+(target-episodeTotal horizon values)
def runningBudget (target : ℝ) (cost : ℕ→ℝ) (time : ℕ) : ℝ :=
  target-∑ step∈Finset.range time,cost step

theorem actual_return_to_go_is_total_minus_prefix (horizon time : ℕ)
    (values : ℕ→ℝ) (ht : time≤horizon) :
    remainingSum horizon time values=episodeTotal horizon values-∑ step∈Finset.range time,values step := by
  exact Finset.sum_Ico_eq_sub values ht

theorem actual_shifted_initial_token (target : ℝ) (horizon : ℕ) (values : ℕ→ℝ) :
    shiftedToken target horizon 0 values=target := by
  rw [shiftedToken,actual_return_to_go_is_total_minus_prefix _ _ _ (Nat.zero_le _)]
  simp

theorem actual_relabel_shifts_and_target (horizon : ℕ) (reward cost : ℕ→ℝ)
    (hr : episodeTotal horizon reward=6) (hc : episodeTotal horizon cost=5) :
    (∀ time,shiftedToken 9 horizon time reward=remainingSum horizon time reward+3) ∧
    (∀ time,shiftedToken 10 horizon time cost=remainingSum horizon time cost+5) ∧
    shiftedToken 9 horizon 0 reward=9 ∧ shiftedToken 10 horizon 0 cost=10 := by
  refine ⟨?_,?_,actual_shifted_initial_token _ _ _,actual_shifted_initial_token _ _ _⟩
  · intro time;norm_num [shiftedToken,hr]
  · intro time;norm_num [shiftedToken,hc]

def relabeledExample {Action : Type*} (targetReward targetCost : ℝ) (horizon : ℕ)
    (reward cost : ℕ→ℝ) (actions : ℕ→Action) : (ℕ→ℝ)×(ℕ→ℝ)×(ℕ→Action) :=
  (fun time=>shiftedToken targetReward horizon time reward,
   fun time=>shiftedToken targetCost horizon time cost,actions)

theorem actual_relabel_keeps_original_actions {Action : Type*}
    (targetReward targetCost : ℝ) (horizon : ℕ) (reward cost : ℕ→ℝ) (actions : ℕ→Action) :
    (relabeledExample targetReward targetCost horizon reward cost actions).2.2=actions := rfl

theorem actual_nonnegative_remaining_cost (horizon time : ℕ) (cost : ℕ→ℝ)
    (hc : ∀ step,0≤cost step) : 0≤remainingSum horizon time cost := by
  exact Finset.sum_nonneg (fun step _=>hc step)

theorem actual_nonnegative_training_cost_tokens (target : ℝ) (horizon time : ℕ)
    (cost : ℕ→ℝ) (hc : ∀ step,0≤cost step) (ht : episodeTotal horizon cost≤target) :
    0 ≤ shiftedToken target horizon time cost := by
  unfold shiftedToken
  linarith [actual_nonnegative_remaining_cost horizon time cost hc]

theorem actual_relabel_budget_invariant (target : ℝ) (horizon time : ℕ)
    (cost : ℕ→ℝ) (ht : time≤horizon) :
    shiftedToken target horizon time cost=runningBudget target cost time := by
  rw [shiftedToken,actual_return_to_go_is_total_minus_prefix _ _ _ ht,runningBudget]
  ring

theorem actual_online_budget_recursion (target : ℝ) (cost : ℕ→ℝ) (time : ℕ) :
    runningBudget target cost (time+1)=runningBudget target cost time-cost time := by
  rw [runningBudget,Finset.sum_range_succ,runningBudget]
  ring

theorem actual_nonnegative_budget_iff_episode_prefix_feasible
    (target : ℝ) (cost : ℕ→ℝ) (time : ℕ) :
    0≤runningBudget target cost time↔(∑ step∈Finset.range time,cost step)≤target := by
  unfold runningBudget
  exact sub_nonneg

def overshootCost (step : ℕ) : ℝ := if step=0 then 11 else 0

theorem actual_nonnegative_cost_overshoots_and_leaves_training_token_domain :
    (∀ step,0≤overshootCost step) ∧ runningBudget 10 overshootCost 0=10 ∧
    runningBudget 10 overshootCost 1= -1 ∧
    runningBudget 10 overshootCost 1∉Ici (0:ℝ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro step;unfold overshootCost;split_ifs <;> norm_num
  all_goals norm_num [runningBudget,overshootCost,Finset.sum_range_succ]

end SafeLearning.CompletePolicyCDTTokens
