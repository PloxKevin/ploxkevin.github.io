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
      have hp : (1/2 : ℝ)^(n+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      split_ifs <;> constructor <;> nlinarith
  · rcases actual_every_history_is_safe_zero_or_a_genuine_delayed_failure u with h | ⟨n,hs,hg,hr⟩
    · rw [h.2.2];norm_num
    · rw [hr];exact ⟨pow_nonneg (by norm_num) _,by unfold jumpRisk;exact pow_le_one₀ (by norm_num) (by norm_num)⟩

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
    0≤ multiplier k ∧ multiplier k<1 ∧ 0<actualRisk (delayedController k) ∧
    max 0 (multiplier k+1*actualRisk (delayedController k))=multiplier (k+1) ∧
    multiplier k< multiplier (k+1) := by
  have hp : 0<(1/2 : ℝ)^k := pow_pos (by norm_num) _
  have hu : (1/2 : ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
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
  have hc' : n+1≤Fintype.card X := by simpa only [Fintype.card_fin] using hc
  omega

theorem actual_any_failing_finite_feedback_trajectory_fails_within_state_count
    {X : Type*} [Fintype X] (f : X→X) (failure : Set X) (x : X)
    (h : ∃n,f^[n] x∈failure) : ∃n<Fintype.card X,f^[n] x∈failure := by
  classical
  refine ⟨Nat.find h,actual_first_failure_time_is_strictly_below_finite_state_count f failure x
    (Nat.find h) (Nat.find_spec h) (fun m hm=>Nat.find_min h hm),Nat.find_spec h⟩


local instance (p : Prop) : Decidable p := Classical.propDecidable p

def finiteFeedbackRisk {X : Type*} (f : X→X) (failure : Set X) (gamma : ℝ) (x : X) : ℝ := by
  classical
  exact if h : ∃n,f^[n] x∈failure then gamma^(Nat.find h) else 0

theorem actual_finite_feedback_risk_is_discounted_first_failure_mass
    {X : Type*} (f : X→X) (failure : Set X) (gamma : ℝ) (x : X) :
    HasSum (fun t : ℕ=>gamma^t*(if h : ∃n,f^[n] x∈failure then
      (if t=Nat.find h then 1 else 0) else 0)) (finiteFeedbackRisk f failure gamma x) := by
  classical
  by_cases h : ∃n,f^[n] x∈failure
  · simp only [finiteFeedbackRisk,dif_pos h]
    convert (hasSum_ite_eq (Nat.find h) (gamma^(Nat.find h))) using 1
    ext t;split_ifs with ht <;> simp_all
  · simp [finiteFeedbackRisk,h]

theorem actual_feedback_risk_in_unit_interval {X : Type*} (f : X→X) (failure : Set X)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma≤1) (x : X) :
    finiteFeedbackRisk f failure gamma x∈Icc (0:ℝ) 1 := by
  classical
  unfold finiteFeedbackRisk
  split_ifs <;> constructor <;> (first | exact pow_nonneg hg0 _ | exact pow_le_one₀ hg0 hg1 | norm_num)

theorem actual_feedback_risk_positive_iff_fails {X : Type*} (f : X→X) (failure : Set X)
    (gamma : ℝ) (hg : 0<gamma) (x : X) :
    0<finiteFeedbackRisk f failure gamma x ↔ ∃n,f^[n] x∈failure := by
  classical
  unfold finiteFeedbackRisk
  split_ifs with h
  · simp [h,pow_pos hg]
  · simp [h]

theorem actual_feedback_risk_zero_iff_never_fails {X : Type*} (f : X→X) (failure : Set X)
    (gamma : ℝ) (hg : 0<gamma) (x : X) :
    finiteFeedbackRisk f failure gamma x=0 ↔ ∀n,f^[n] x∉failure := by
  classical
  unfold finiteFeedbackRisk
  split_ifs with h
  · have hp := (pow_pos hg (Nat.find h)).ne'
    simp only [hp,false_iff]
    intro hh;obtain ⟨n,hn⟩ := h;exact hh n hn
  · simp only [true_iff]
    exact fun n hn=>h ⟨n,hn⟩

theorem actual_failing_finite_feedback_risk_has_uniform_discount_lower_bound
    {X : Type*} [Fintype X] (f : X→X) (failure : Set X) (gamma : ℝ)
    (hg0 : 0<gamma) (hg1 : gamma≤1) (x : X) (h : ∃n,f^[n] x∈failure) :
    gamma^(Fintype.card X)≤finiteFeedbackRisk f failure gamma x := by
  classical
  rw [finiteFeedbackRisk,dif_pos h]
  have hn := actual_first_failure_time_is_strictly_below_finite_state_count f failure x (Nat.find h)
    (Nat.find_spec h) (fun m hm=>Nat.find_min h hm)
  exact pow_le_pow_of_le_one hg0.le hg1 hn.le

def expectedFiniteFeedbackRisk {X : Type*} [Fintype X] (weights : X→ℝ)
    (f : X→X) (failure : Set X) (gamma : ℝ) : ℝ :=
  ∑x,weights x*finiteFeedbackRisk f failure gamma x

def positiveMasses {X : Type*} [Fintype X] (weights : X→ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun x=>0<weights x)).image weights

theorem actual_probability_weights_have_nonempty_positive_masses {X : Type*} [Fintype X]
    (weights : X→ℝ) (hsum : ∑x,weights x=1) : (positiveMasses weights).Nonempty := by
  classical
  have h : ∃x,0<weights x := by
    by_contra hn
    have hs : ∑x,weights x≤0 := Finset.sum_nonpos (fun x _=>by push_neg at hn;exact hn x)
    linarith
  obtain ⟨x,hx⟩ := h
  exact ⟨weights x,Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩,rfl⟩⟩

def minimumPositiveMass {X : Type*} [Fintype X] (weights : X→ℝ) (hsum : ∑x,weights x=1) : ℝ :=
  (positiveMasses weights).min' (actual_probability_weights_have_nonempty_positive_masses weights hsum)

theorem actual_minimum_positive_probability_mass_is_positive_and_bounds_each_supported_state
    {X : Type*} [Fintype X] (weights : X→ℝ) (hsum : ∑x,weights x=1) :
    0<minimumPositiveMass weights hsum ∧ ∀x,0<weights x→minimumPositiveMass weights hsum≤weights x := by
  classical
  constructor
  · have hm := Finset.min'_mem (positiveMasses weights)
      (actual_probability_weights_have_nonempty_positive_masses weights hsum)
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
    have hp := (Finset.mem_filter.mp hx).2
    rw [he] at hp;exact hp
  · intro x hx
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩,rfl⟩)

theorem actual_initial_probability_weighted_risk_in_unit_interval
    {X : Type*} [Fintype X] (weights : X→ℝ) (hw : ∀x,0≤weights x) (hsum : ∑x,weights x=1)
    (f : X→X) (failure : Set X) (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma≤1) :
    expectedFiniteFeedbackRisk weights f failure gamma∈Icc (0:ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x _=>mul_nonneg (hw x) (actual_feedback_risk_in_unit_interval f failure gamma hg0 hg1 x).1)
  · unfold expectedFiniteFeedbackRisk
    calc
      _≤∑x,weights x := Finset.sum_le_sum (fun x _=>mul_le_of_le_one_right (hw x)
        (actual_feedback_risk_in_unit_interval f failure gamma hg0 hg1 x).2)
      _=1 := hsum

theorem actual_initial_weighted_risk_zero_iff_safe_at_every_positive_mass_state
    {X : Type*} [Fintype X] (weights : X→ℝ) (hw : ∀x,0≤weights x)
    (f : X→X) (failure : Set X) (gamma : ℝ) (hg0 : 0<gamma) (hg1 : gamma≤1) :
    expectedFiniteFeedbackRisk weights f failure gamma=0 ↔
      ∀x,0<weights x→∀n,f^[n] x∉failure := by
  classical
  constructor
  · intro h x hx
    have hs : weights x*finiteFeedbackRisk f failure gamma x≤expectedFiniteFeedbackRisk weights f failure gamma :=
      Finset.single_le_sum (fun y _=>mul_nonneg (hw y)
        (actual_feedback_risk_in_unit_interval f failure gamma hg0.le hg1 y).1) (Finset.mem_univ x)
    have hr := (actual_feedback_risk_in_unit_interval f failure gamma hg0.le hg1 x).1
    have hz : finiteFeedbackRisk f failure gamma x=0 := by rw [h] at hs;nlinarith
    exact (actual_feedback_risk_zero_iff_never_fails f failure gamma hg0 x).mp hz
  · intro h
    unfold expectedFiniteFeedbackRisk
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : 0<weights x
    · rw [(actual_feedback_risk_zero_iff_never_fails f failure gamma hg0 x).mpr (h x hx),mul_zero]
    · have hz : weights x=0 := le_antisymm (le_of_not_gt hx) (hw x)
      rw [hz,zero_mul]

theorem actual_positive_expected_feedback_risk_has_uniform_mass_discount_lower_bound
    {X : Type*} [Fintype X] (weights : X→ℝ) (hw : ∀x,0≤weights x) (hsum : ∑x,weights x=1)
    (f : X→X) (failure : Set X) (gamma : ℝ) (hg0 : 0<gamma) (hg1 : gamma≤1)
    (hu : 0<expectedFiniteFeedbackRisk weights f failure gamma) :
    minimumPositiveMass weights hsum*gamma^(Fintype.card X)≤expectedFiniteFeedbackRisk weights f failure gamma := by
  classical
  have hex : ∃x,0<weights x ∧ ∃n,f^[n] x∈failure := by
    by_contra hn
    have hs : ∀x,0<weights x→∀n,f^[n] x∉failure := by
      intro x hx n hf;exact hn ⟨x,hx,n,hf⟩
    have hz := (actual_initial_weighted_risk_zero_iff_safe_at_every_positive_mass_state weights hw f failure gamma hg0 hg1).mpr hs
    linarith
  obtain ⟨x,hx,hfail⟩ := hex
  have hm := (actual_minimum_positive_probability_mass_is_positive_and_bounds_each_supported_state weights hsum).2 x hx
  have hr := actual_failing_finite_feedback_risk_has_uniform_discount_lower_bound f failure gamma hg0 hg1 x hfail
  have ht : weights x*finiteFeedbackRisk f failure gamma x≤expectedFiniteFeedbackRisk weights f failure gamma :=
    Finset.single_le_sum (fun y _=>mul_nonneg (hw y)
      (actual_feedback_risk_in_unit_interval f failure gamma hg0.le hg1 y).1) (Finset.mem_univ x)
  exact (mul_le_mul hm hr (pow_nonneg hg0.le _) hx.le).trans ht

theorem actual_finite_feedback_dual_search_stops_with_a_constant_positive_step
    {X : Type*} [Fintype X] (weights : X→ℝ) (hw : ∀x,0≤weights x) (hsum : ∑x,weights x=1)
    (policies : ℕ→X→X) (failure : Set X) (gamma eta threshold : ℝ)
    (hg0 : 0<gamma) (hg1 : gamma≤1) (heta : 0<eta) (lambda : ℕ→ℝ)
    (hupdate : ∀n,lambda (n+1)=max 0 (lambda n+eta*expectedFiniteFeedbackRisk weights (policies n) failure gamma))
    (hsafeabove : ∀n,threshold<lambda n→expectedFiniteFeedbackRisk weights (policies n) failure gamma=0) :
    ∃n,expectedFiniteFeedbackRisk weights (policies n) failure gamma=0 := by
  by_contra hnone
  have hpositive : ∀n,0<expectedFiniteFeedbackRisk weights (policies n) failure gamma := by
    intro n
    have hh := (actual_initial_probability_weighted_risk_in_unit_interval weights hw hsum (policies n) failure gamma hg0.le hg1).1
    exact lt_of_le_of_ne hh (Ne.symm (fun hz=>hnone ⟨n,hz⟩))
  let c := minimumPositiveMass weights hsum*gamma^(Fintype.card X)
  have hc : 0<c := mul_pos (actual_minimum_positive_probability_mass_is_positive_and_bounds_each_supported_state weights hsum).1 (pow_pos hg0 _)
  have hlow : ∀n,c≤expectedFiniteFeedbackRisk weights (policies n) failure gamma := by
    intro n;exact actual_positive_expected_feedback_risk_has_uniform_mass_discount_lower_bound weights hw hsum (policies n) failure gamma hg0 hg1 (hpositive n)
  have hlinear : ∀n,lambda 0+(n:ℝ)*(eta*c)≤lambda n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := le_max_right (0:ℝ) (lambda n+eta*expectedFiniteFeedbackRisk weights (policies n) failure gamma)
      have he := mul_le_mul_of_nonneg_left (hlow n) heta.le
      rw [←hupdate n] at hs
      push_cast
      nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((threshold-lambda 0)/(eta*c))
  have hc' : 0<eta*c := mul_pos heta hc
  have ht : threshold<lambda n := by
    have hh := (div_lt_iff₀ hc').mp hn
    have hl := hlinear n
    nlinarith
  exact hnone ⟨n,hsafeabove n ht⟩

end SafeLearning.CompleteModulesViabilityDualClock30
