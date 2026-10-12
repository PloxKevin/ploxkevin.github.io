import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Set
namespace SafeLearning.CompleteModulesViabilityDualClock30

-- none is the terminated failure bookkeeping state; surviving clock n is some n.
def nextState : Option ℕ → Bool → Option ℕ
  | none, _ => none
  | some n, true => none
  | some n, false => some (n+1)
def sourcePath (u : ℕ → Bool) : ℕ → Option ℕ
  | 0 => some 0
  | t+1 => nextState (sourcePath u t) (u t)
def sourceReward (u : ℕ → Bool) (t : ℕ) : ℝ :=
  match sourcePath u t with
  | none => 0
  | some n => if u t then (1/2)*(1-(1/2 : ℝ)^(n+1)) else 0
def sourceFailureMass (u : ℕ → Bool) (t : ℕ) : ℝ :=
  if 0<t ∧ sourcePath u (t-1)≠none ∧ sourcePath u t=none then 1 else 0
def gainTerm (u : ℕ → Bool) (t : ℕ) : ℝ := (1/2 : ℝ)^t*sourceReward u t
def riskTerm (u : ℕ → Bool) (t : ℕ) : ℝ := (1/2 : ℝ)^t*sourceFailureMass u t
def actualGain (u : ℕ → Bool) : ℝ := ∑' t,gainTerm u t
def actualRisk (u : ℕ → Bool) : ℝ := ∑' t,riskTerm u t
def lagrangian (lambda : ℝ) (u : ℕ → Bool) : ℝ := actualGain u-lambda*actualRisk u
def safeController : ℕ → Bool := fun _=>false
def delayedController (n : ℕ) : ℕ → Bool := fun t=>decide (t=n)
def multiplier (n : ℕ) : ℝ := 1-(1/2 : ℝ)^n
def jumpRisk (n : ℕ) : ℝ := (1/2 : ℝ)^(n+1)
def actualSafe (u : ℕ → Bool) : Prop := ∀t,sourcePath u t≠none

theorem actual_arbitrary_history_before_first_jump (u : ℕ → Bool) (n : ℕ)
    (hb : ∀t<n,u t=false) : ∀t≤n,sourcePath u t=some t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => simp [sourcePath,nextState,ih (by omega),hb t (by omega)]

theorem actual_first_jump_enters_failure_and_terminates (u : ℕ → Bool) (n : ℕ)
    (hj : u n=true) (hb : ∀t<n,u t=false) :
    sourcePath u (n+1)=none ∧ ∀k,sourcePath u (n+1+k)=none := by
  have hf : sourcePath u (n+1)=none := by
    simp [sourcePath,nextState,actual_arbitrary_history_before_first_jump u n hb n le_rfl,hj]
  refine ⟨hf,?_⟩
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [show n+1+(k+1)=(n+1+k)+1 by omega,sourcePath]
    simp [nextState,ih]

theorem actual_first_jump_entire_gain_and_risk_terms (u : ℕ → Bool) (n : ℕ)
    (hj : u n=true) (hb : ∀t<n,u t=false) :
    (∀t,gainTerm u t=if t=n then jumpRisk n*(1-jumpRisk n) else 0) ∧
    (∀t,riskTerm u t=if t=n+1 then jumpRisk n else 0) := by
  have hp := actual_arbitrary_history_before_first_jump u n hb
  have hf := actual_first_jump_enters_failure_and_terminates u n hj hb
  constructor
  · intro t
    by_cases hl : t<n
    · simp [gainTerm,sourceReward,hp t hl.le,hb t hl,ne_of_lt hl]
    by_cases he : t=n
    · subst t
      simp [gainTerm,sourceReward,hp n le_rfl,hj,jumpRisk,pow_succ]
      ring
    have hpost : n+1≤t := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hpost
    simp [gainTerm,sourceReward,hf.2 k,he]
  · intro t
    by_cases hz : t=0
    · subst t;simp [riskTerm,sourceFailureMass]
    by_cases he : t=n+1
    · subst t
      simp [riskTerm,sourceFailureMass,hp n le_rfl,hf.1,jumpRisk]
    by_cases hl : t≤n
    · simp [riskTerm,sourceFailureMass,hp t hl,he]
    have hg : n+2≤t := by omega
    have hm : n+1≤t-1 := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hm
    have hnone : sourcePath u (t-1)=none := by rw [hk];exact hf.2 k
    simp [riskTerm,sourceFailureMass,hnone,he]

theorem actual_first_jump_full_infinite_gain_and_risk (u : ℕ → Bool) (n : ℕ)
    (hj : u n=true) (hb : ∀t<n,u t=false) :
    HasSum (gainTerm u) (jumpRisk n*(1-jumpRisk n)) ∧
    HasSum (riskTerm u) (jumpRisk n) ∧
    actualGain u=jumpRisk n*(1-jumpRisk n) ∧ actualRisk u=jumpRisk n := by
  have h := actual_first_jump_entire_gain_and_risk_terms u n hj hb
  have hg : gainTerm u=(fun t=>if t=n then jumpRisk n*(1-jumpRisk n) else 0) := funext h.1
  have hr : riskTerm u=(fun t=>if t=n+1 then jumpRisk n else 0) := funext h.2
  have g : HasSum (gainTerm u) (jumpRisk n*(1-jumpRisk n)) := by rw [hg];exact hasSum_ite_eq _ _
  have r : HasSum (riskTerm u) (jumpRisk n) := by rw [hr];exact hasSum_ite_eq _ _
  exact ⟨g,r,g.tsum_eq,r.tsum_eq⟩

theorem actual_never_jumping_full_gain_and_risk_are_zero (u : ℕ → Bool)
    (hu : ∀t,u t=false) :
    actualSafe u ∧ (∀t,gainTerm u t=0 ∧ riskTerm u t=0) ∧ actualGain u=0 ∧ actualRisk u=0 := by
  have hp : ∀t,sourcePath u t=some t := by
    intro t;exact actual_arbitrary_history_before_first_jump u t (fun s _=>hu s) t le_rfl
  have hzero : ∀t,gainTerm u t=0 ∧ riskTerm u t=0 := by
    intro t;simp [gainTerm,sourceReward,riskTerm,sourceFailureMass,hp t,hu t]
  refine ⟨fun t=>by rw [hp t];simp,hzero,?_,?_⟩
  · simp [actualGain,funext (fun t=>(hzero t).1)]
  · simp [actualRisk,funext (fun t=>(hzero t).2)]

theorem actual_every_history_is_safe_zero_or_a_genuine_delayed_failure (u : ℕ → Bool) :
    (actualSafe u ∧ actualGain u=0 ∧ actualRisk u=0) ∨
    ∃n,¬actualSafe u ∧ actualGain u=jumpRisk n*(1-jumpRisk n) ∧ actualRisk u=jumpRisk n := by
  classical
  by_cases h : ∃n,u n=true
  · let n := Nat.find h
    have hj : u n=true := Nat.find_spec h
    have hb : ∀t<n,u t=false := by
      intro t ht;have hn := Nat.find_min h ht;cases he : u t <;> simp_all
    have hv := actual_first_jump_full_infinite_gain_and_risk u n hj hb
    refine Or.inr ⟨n,?_,hv.2.2.1,hv.2.2.2⟩
    intro hs;have hf := (actual_first_jump_enters_failure_and_terminates u n hj hb).1
    exact hs (n+1) hf
  · have hu : ∀t,u t=false := by intro t;cases he : u t <;> simp_all
    have hs := actual_never_jumping_full_gain_and_risk_are_zero u hu
    exact Or.inl ⟨hs.1,hs.2.2.1,hs.2.2.2⟩

theorem actual_delayed_controller_values (n : ℕ) :
    ¬actualSafe (delayedController n) ∧ actualGain (delayedController n)=jumpRisk n*(1-jumpRisk n) ∧
    actualRisk (delayedController n)=jumpRisk n := by
  have hj : delayedController n n=true := by simp [delayedController]
  have hb : ∀t<n,delayedController n t=false := by intro t ht;simp [delayedController,ne_of_lt ht]
  have h := actual_first_jump_full_infinite_gain_and_risk (delayedController n) n hj hb
  refine ⟨?_,h.2.2.1,h.2.2.2⟩
  intro hs;exact hs (n+1) (actual_first_jump_enters_failure_and_terminates _ n hj hb).1

theorem actual_safe_controller_values : actualSafe safeController ∧ actualGain safeController=0 ∧ actualRisk safeController=0 := by
  have h := actual_never_jumping_full_gain_and_risk_are_zero safeController (by simp [safeController])
  exact ⟨h.1,h.2.2.1,h.2.2.2⟩

theorem actual_rewards_are_bounded_nonnegative_and_all_risks_are_in_unit_interval
    (u : ℕ → Bool) : (∀t,sourceReward u t∈Icc (0:ℝ) (1/2)) ∧ actualRisk u∈Icc (0:ℝ) 1 := by
  constructor
  · intro t
    unfold sourceReward
    cases sourcePath u t with
    | none => norm_num
    | some n =>
      have hn := pow_nonneg (by norm_num : (0:ℝ)≤1/2) (n+1)
      have hp := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) (n+1)
      split_ifs <;> constructor <;> nlinarith
  · rcases actual_every_history_is_safe_zero_or_a_genuine_delayed_failure u with h | ⟨n,hs,hg,hr⟩
    · rw [h.2.2];norm_num
    · rw [hr];exact ⟨pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num) _⟩

theorem actual_risk_zero_iff_safe (u : ℕ → Bool) : actualRisk u=0 ↔ actualSafe u := by
  rcases actual_every_history_is_safe_zero_or_a_genuine_delayed_failure u with h | ⟨n,hs,hg,hr⟩
  · simp [h.1,h.2.2]
  · have hp : 0<jumpRisk n := pow_pos (by norm_num) _
    simp [hr,hs,hp.ne']

theorem actual_all_penalties_above_one_make_every_global_maximizer_safe (lambda : ℝ) (hl : 1<lambda)
    (u : ℕ → Bool) (hmax : ∀v,lagrangian lambda v≤lagrangian lambda u) : actualSafe u := by
  rcases actual_every_history_is_safe_zero_or_a_genuine_delayed_failure u with h | ⟨n,hs,hg,hr⟩
  · exact h.1
  · have h := hmax safeController
    have hp : 0<jumpRisk n := pow_pos (by norm_num) _
    simp only [lagrangian,actual_safe_controller_values.2.1,actual_safe_controller_values.2.2,hg,hr] at h
    nlinarith [sq_pos_of_pos hp]

theorem actual_each_iterate_controller_is_a_global_lagrangian_maximizer (k : ℕ) :
    ∀u,lagrangian (multiplier k) u≤lagrangian (multiplier k) (delayedController k) := by
  intro u
  have hk := actual_delayed_controller_values k
  have hpow : (1/2 : ℝ)^k=2*jumpRisk k := by simp [jumpRisk,pow_succ];ring
  rcases actual_every_history_is_safe_zero_or_a_genuine_delayed_failure u with h | ⟨n,hs,hg,hr⟩
  · simp only [lagrangian,h.2.1,h.2.2,hk.2.1,hk.2.2,multiplier]
    rw [hpow];nlinarith [sq_nonneg (jumpRisk k)]
  · simp only [lagrangian,hg,hr,hk.2.1,hk.2.2,multiplier]
    rw [hpow];nlinarith [sq_nonneg (jumpRisk n-jumpRisk k)]

theorem actual_projected_update_is_exact_and_never_stops (k : ℕ) :
    0≤multiplier k ∧ multiplier k<1 ∧ 0<actualRisk (delayedController k) ∧
    max 0 (multiplier k+1*actualRisk (delayedController k))=multiplier (k+1) ∧
    multiplier k<multiplier (k+1) := by
  have hp : 0<(1/2 : ℝ)^k := pow_pos (by norm_num) _
  have hu : (1/2 : ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num) _
  have hr := (actual_delayed_controller_values k).2.2
  have hq : 0<jumpRisk k := pow_pos (by norm_num) _
  have he : multiplier k+1*actualRisk (delayedController k)=multiplier (k+1) := by
    rw [hr];simp [multiplier,jumpRisk,pow_succ];ring
  refine ⟨by unfold multiplier;linarith,by unfold multiplier;linarith,by rw [hr];exact hq,?_,?_⟩
  · rw [he,max_eq_right];unfold multiplier;rw [pow_succ];nlinarith
  · unfold multiplier;rw [pow_succ];nlinarith

theorem actual_nontermination_with_exact_maximizers_despite_a_finite_safe_penalty :
    (∀k,¬actualSafe (delayedController k) ∧
      (∀u,lagrangian (multiplier k) u≤lagrangian (multiplier k) (delayedController k)) ∧
      max 0 (multiplier k+actualRisk (delayedController k))=multiplier (k+1) ∧ multiplier k<1) ∧
    (∀lambda : ℝ,1<lambda→∀u,(∀v,lagrangian lambda v≤lagrangian lambda u)→actualSafe u) := by
  constructor
  · intro k
    have h := actual_projected_update_is_exact_and_never_stops k
    exact ⟨(actual_delayed_controller_values k).1,actual_each_iterate_controller_is_a_global_lagrangian_maximizer k,
      by simpa using h.2.2.2.1,h.2.1⟩
  · exact actual_all_penalties_above_one_make_every_global_maximizer_safe

-- The uniform finite-state failure-time bound follows from actual feedback iterates.
private theorem no_repeated_state_before_a_first_failure {X : Type*} (f : X→X)
    (failure : Set X) (x : X) (n : ℕ) (hf : f^[n] x∈failure)
    (hb : ∀m<n,f^[m] x∉failure) (i j : ℕ) (hi : i<j) (hj : j≤n)
    (he : f^[i] x=f^[j] x) : False := by
  have h := congrArg (f^[n-j]) he
  have hleft : f^[n-j] (f^[i] x)=f^[n-j+i] x := (Function.iterate_add_apply f _ _ _).symm
  have hright : f^[n-j] (f^[j] x)=f^[n] x := by
    rw [←Function.iterate_add_apply,show n-j+j=n by omega]
  rw [hleft,hright] at h
  exact hb (n-j+i) (by omega) (h.symm ▸ hf)

theorem actual_first_failure_time_is_strictly_below_finite_state_count
    {X : Type*} [Fintype X] (f : X→X) (failure : Set X) (x : X) (n : ℕ)
    (hf : f^[n] x∈failure) (hb : ∀m<n,f^[m] x∉failure) : n<Fintype.card X := by
  have hi : Function.Injective (fun i : Fin (n+1)=>f^[i.val] x) := by
    intro i j he
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact no_repeated_state_before_a_first_failure f failure x n hf hb i j h (by omega) he
    · exact no_repeated_state_before_a_first_failure f failure x n hf hb j i h (by omega) he.symm
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_fin] using hc

theorem actual_any_failing_finite_feedback_trajectory_fails_within_state_count
    {X : Type*} [Fintype X] (f : X→X) (failure : Set X) (x : X)
    (h : ∃n,f^[n] x∈failure) : ∃n<Fintype.card X,f^[n] x∈failure := by
  classical
  refine ⟨Nat.find h,actual_first_failure_time_is_strictly_below_finite_state_count f failure x
    (Nat.find h) (Nat.find_spec h) (fun m hm=>Nat.find_min h hm),Nat.find_spec h⟩

end SafeLearning.CompleteModulesViabilityDualClock30
