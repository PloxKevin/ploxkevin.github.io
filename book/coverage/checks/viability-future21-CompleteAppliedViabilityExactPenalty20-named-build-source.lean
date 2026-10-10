import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Set
namespace SafeLearning.CompleteAppliedViabilityExactPenalty20

/-- States are A, failure, and the zero-reward absorbing state. True means jump. -/
def nextState (s : Fin 3) (jump : Bool) : Fin 3 :=
  if s = 0 then (if jump then 1 else 0) else 2
def sourcePath (u : ℕ → Bool) : ℕ → Fin 3
  | 0 => 0
  | t+1 => nextState (sourcePath u t) (u t)
def sourceReward (p : ℝ) (u : ℕ → Bool) (t : ℕ) : ℝ :=
  if sourcePath u t = 0 then (if u t then 4 else 1)
  else if sourcePath u t = 1 then -p else 0
def sourceTerm (p : ℝ) (u : ℕ → Bool) (t : ℕ) : ℝ := (1/2 : ℝ)^t*sourceReward p u t
def sourceReturn (p : ℝ) (u : ℕ → Bool) : ℝ := ∑' t, sourceTerm p u t
def delayReward (p : ℝ) (n t : ℕ) : ℝ :=
  if t<n then 1 else if t=n then 4 else if t=n+1 then -p else 0
def delayTerm (p : ℝ) (n t : ℕ) : ℝ := (1/2 : ℝ)^t*delayReward p n t
def safeController : ℕ → Bool := fun _ => false
def immediateJump : ℕ → Bool := fun t => decide (t=0)

theorem actual_arbitrary_controller_before_first_jump_stays_in_A
    (u : ℕ → Bool) (n : ℕ) (hbefore : ∀ t<n, u t=false) :
    ∀ t≤n, sourcePath u t=0 := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have htn : t<n := by omega
    simp [sourcePath,nextState,ih (by omega),hbefore t htn]

theorem actual_first_jump_path_and_full_reward_sequence
    (p : ℝ) (u : ℕ → Bool) (n : ℕ) (hjump : u n=true)
    (hbefore : ∀ t<n,u t=false) :
    (sourcePath u (n+1)=1 ∧ sourcePath u (n+2)=2) ∧
      ∀ t, sourceTerm p u t=delayTerm p n t := by
  have hpre := actual_arbitrary_controller_before_first_jump_stays_in_A u n hbefore
  have hfail : sourcePath u (n+1)=1 := by simp [sourcePath,nextState,hpre n le_rfl,hjump]
  have hdone : sourcePath u (n+2)=2 := by
    change nextState (sourcePath u (n+1)) (u (n+1))=2
    simp [nextState,hfail]
  have hpost : ∀ k, sourcePath u (n+2+k)=2 := by
    intro k
    induction k with
    | zero => simpa using hdone
    | succ k ih =>
      rw [show n+2+(k+1)=(n+2+k)+1 by omega,sourcePath]
      simp [nextState,ih]
  refine ⟨⟨hfail,hdone⟩,?_⟩
  intro t
  by_cases ht : t<n
  · simp [sourceTerm,sourceReward,delayTerm,delayReward,ht,hpre t ht.le,hbefore t ht]
  by_cases he : t=n
  · subst t
    simp [sourceTerm,sourceReward,delayTerm,delayReward,hpre n le_rfl,hjump]
  by_cases hf : t=n+1
  · subst t
    simp [sourceTerm,sourceReward,delayTerm,delayReward,hfail]
  have hg : n+2≤t := by omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hg
  simp [sourceTerm,sourceReward,delayTerm,delayReward,hpost k,ht,he,hf]

theorem actual_every_controller_has_a_safe_or_a_first_jump_reward_sequence
    (p : ℝ) (u : ℕ → Bool) :
    (∀ t, sourceTerm p u t=(1/2 : ℝ)^t) ∨ ∃n,∀t,sourceTerm p u t=delayTerm p n t := by
  classical
  by_cases h : ∃n,u n=true
  · let n := Nat.find h
    have hn : u n=true := Nat.find_spec h
    have hb : ∀t<n,u t=false := by
      intro t ht
      have hh : ¬u t=true := Nat.find_min h ht
      cases he : u t <;> simp_all
    exact Or.inr ⟨n,(actual_first_jump_path_and_full_reward_sequence p u n hn hb).2⟩
  · left
    have hu : ∀t,u t=false := by
      intro t
      cases he : u t <;> simp_all
    intro t
    have hs := actual_arbitrary_controller_before_first_jump_stays_in_A u t (fun s _ => hu s)
    simp [sourceTerm,sourceReward,hs t le_rfl,hu t]

theorem actual_safe_geometric_series_has_sum_two :
    HasSum (fun t : ℕ => (1/2 : ℝ)^t) 2 := by
  convert hasSum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)|<1) using 1 <;> norm_num

theorem actual_prefix_geometric_sum (n : ℕ) :
    (∑t∈Finset.range n,(1/2 : ℝ)^t)=2-2*(1/2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ];ring

theorem actual_delayed_jump_full_series_has_the_printed_value (p : ℝ) (n : ℕ) :
    HasSum (delayTerm p n) (2+(1/2 : ℝ)^n*((4-p/2)-2)) := by
  have hh : HasSum (delayTerm p n) (∑t∈Finset.range (n+2),delayTerm p n t) := by
    apply hasSum_sum_of_ne_finset_zero
    intro t ht
    have h : n+2≤t := by simpa only [Finset.mem_range,not_lt] using ht
    simp [delayTerm,delayReward,show ¬t<n by omega,show t≠n by omega,show t≠n+1 by omega]
  have hprefix : (∑t∈Finset.range n,delayTerm p n t)=∑t∈Finset.range n,(1/2 : ℝ)^t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [delayTerm,delayReward,Finset.mem_range.mp ht]
  convert hh using 1
  rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
    hprefix,actual_prefix_geometric_sum]
  simp [delayTerm,delayReward,pow_succ]
  ring

theorem actual_every_controller_full_series_is_summable_and_has_one_of_all_values
    (p : ℝ) (u : ℕ → Bool) :
    Summable (sourceTerm p u) ∧
      (sourceReturn p u=2 ∨ ∃n,sourceReturn p u=2+(1/2 : ℝ)^n*((4-p/2)-2)) := by
  rcases actual_every_controller_has_a_safe_or_a_first_jump_reward_sequence p u with h | ⟨n,h⟩
  · have he : sourceTerm p u=(fun t : ℕ => (1/2 : ℝ)^t) := funext h
    rw [he]
    exact ⟨actual_safe_geometric_series_has_sum_two.summable,
      Or.inl (by simpa [sourceReturn,he] using actual_safe_geometric_series_has_sum_two.tsum_eq)⟩
  · have he : sourceTerm p u=delayTerm p n := funext h
    rw [he]
    exact ⟨(actual_delayed_jump_full_series_has_the_printed_value p n).summable,
      Or.inr ⟨n,by simpa [sourceReturn,he] using
        (actual_delayed_jump_full_series_has_the_printed_value p n).tsum_eq⟩⟩

theorem actual_safe_value_two_and_immediate_jump_value (p : ℝ) :
    sourceReturn p safeController=2 ∧ sourceReturn p immediateJump=4-p/2 := by
  constructor
  · have hp : ∀t,sourcePath safeController t=0 := by
      intro t
      exact actual_arbitrary_controller_before_first_jump_stays_in_A _ t (by simp [safeController]) t le_rfl
    unfold sourceReturn
    simp only [sourceTerm,sourceReward,hp,ite_true,safeController,Bool.false_eq_true,ite_false,mul_one]
    exact actual_safe_geometric_series_has_sum_two.tsum_eq
  · have h := (actual_first_jump_path_and_full_reward_sequence p immediateJump 0
      (by simp [immediateJump]) (by omega)).2
    have he : sourceTerm p immediateJump=delayTerm p 0 := funext h
    unfold sourceReturn
    rw [he,(actual_delayed_jump_full_series_has_the_printed_value p 0).tsum_eq]
    norm_num

theorem actual_all_controller_returns_are_bounded_by_safe_or_immediate_value
    (p : ℝ) (u : ℕ → Bool) : sourceReturn p u ≤ max 2 (4-p/2) := by
  rcases (actual_every_controller_full_series_is_summable_and_has_one_of_all_values p u).2
      with h | ⟨n,h⟩
  · rw [h];exact le_max_left _ _
  · rw [h]
    have hp : 0≤(1/2 : ℝ)^n := pow_nonneg (by norm_num) n
    have hu : (1/2 : ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    by_cases hb : 0≤(4-p/2)-2
    · apply le_trans _ (le_max_right _ _)
      nlinarith [mul_le_mul_of_nonneg_right hu hb]
    · apply le_trans _ (le_max_left _ _)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_ge hb)]

def optimalInitialActions (p : ℝ) : Set Bool :=
  {a | ∃u : ℕ → Bool, u 0=a ∧ ∀v,sourceReturn p v ≤ sourceReturn p u}

theorem actual_every_optimal_initial_action_is_safe_iff_penalty_strictly_exceeds_four
    (p : ℝ) : (∀a∈optimalInitialActions p,a=false) ↔ 4<p := by
  constructor
  · intro hall
    by_contra hn
    have hp : p≤4 := le_of_not_gt hn
    have hopt : true∈optimalInitialActions p := by
      refine ⟨immediateJump,by simp [immediateJump],?_⟩
      intro v
      rw [(actual_safe_value_two_and_immediate_jump_value p).2]
      exact (actual_all_controller_returns_are_bounded_by_safe_or_immediate_value p v).trans
        (by rw [max_eq_right (by linarith)])
    have := hall true hopt
    contradiction
  · intro hp a ha
    rcases ha with ⟨u,hu,hmax⟩
    cases a with
    | false => rfl
    | true =>
      have he := (actual_first_jump_path_and_full_reward_sequence p u 0 hu (by omega)).2
      have hv : sourceReturn p u=4-p/2 := by
        unfold sourceReturn
        rw [show sourceTerm p u=delayTerm p 0 from funext he,
          (actual_delayed_jump_full_series_has_the_printed_value p 0).tsum_eq]
        norm_num
      have h := hmax safeController
      rw [(actual_safe_value_two_and_immediate_jump_value p).1,hv] at h
      linarith

theorem actual_threshold_tie_and_strict_delay_loss (n : ℕ) :
    sourceReturn 4 safeController=sourceReturn 4 immediateJump ∧
      (∀p : ℝ,p<4 → 0<n → 2+(1/2 : ℝ)^n*((4-p/2)-2)<4-p/2) := by
  refine ⟨by rw [(actual_safe_value_two_and_immediate_jump_value 4).1,
    (actual_safe_value_two_and_immediate_jump_value 4).2];norm_num,?_⟩
  intro p hp hn
  have hpow : (1/2 : ℝ)^n<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hb : 0<(4-p/2)-2 := by linarith
  nlinarith [mul_lt_mul_of_pos_right hpow hb]

end SafeLearning.CompleteAppliedViabilityExactPenalty20
