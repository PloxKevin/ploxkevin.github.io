import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedViabilityKernel

def stateConstraint : Set ℝ := Icc (-1) 1
def inputConstraint : Set ℝ := Icc (-(3/10)) (3/10)
def nextState (state input : ℝ) : ℝ := (3/2)*state+input
def predecessor (target : Set ℝ) : Set ℝ :=
  {state | ∃input ∈ inputConstraint,nextState state input ∈ target}
def backwardSet : ℕ→Set ℝ
  | 0 => stateConstraint
  | n+1 => backwardSet n ∩ predecessor (backwardSet n)
def radius (n : ℕ) : ℝ := 3/5+(2/5)*(2/3:ℝ)^n

theorem actual_predecessor_of_every_nonnegative_symmetric_interval (c : ℝ) (hc : 0≤c) :
    predecessor (Icc (-c) c)=Icc (-(c+3/10)/(3/2)) ((c+3/10)/(3/2)) := by
  ext x
  constructor
  · rintro ⟨u,hu,hnext⟩
    change -(3/10:ℝ)≤u ∧ u≤3/10 at hu
    change -c≤(3/2)*x+u ∧ (3/2)*x+u≤c at hnext
    change -(c+3/10)/(3/2)≤x ∧ x≤(c+3/10)/(3/2)
    constructor <;> linarith
  · intro hx
    change -(c+3/10)/(3/2)≤x ∧ x≤(c+3/10)/(3/2) at hx
    by_cases hupper : c<(3/2)*x
    · refine ⟨c-(3/2)*x,?_,?_⟩
      · change -(3/10:ℝ)≤c-(3/2)*x ∧ c-(3/2)*x≤3/10
        constructor <;> linarith
      · change -c≤(3/2)*x+(c-(3/2)*x) ∧ (3/2)*x+(c-(3/2)*x)≤c
        constructor <;> linarith
    · by_cases hlower : (3/2)*x< -c
      · refine ⟨-c-(3/2)*x,?_,?_⟩
        · change -(3/10:ℝ)≤ -c-(3/2)*x ∧ -c-(3/2)*x≤3/10
          constructor <;> linarith
        · change -c≤(3/2)*x+(-c-(3/2)*x) ∧ (3/2)*x+(-c-(3/2)*x)≤c
          constructor <;> linarith
      · refine ⟨0,by norm_num [inputConstraint],?_⟩
        change -c≤(3/2)*x+0 ∧ (3/2)*x+0≤c
        constructor <;> linarith

theorem actual_predecessor_membership_is_the_literal_absolute_value_test
    (c x : ℝ) (hc : 0≤c) :
    x∈predecessor (Icc (-c) c) ↔ |(3/2)*x|≤c+3/10 := by
  rw [actual_predecessor_of_every_nonnegative_symmetric_interval c hc]
  rw [abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem actual_backward_radius_recurrence_and_geometric_formula (n : ℕ) :
    3/5≤radius n ∧ 0≤radius n ∧ radius (n+1)=(radius n+3/10)/(3/2) ∧
      radius (n+1)≤radius n ∧
      radius (n+1)=min (radius n) ((radius n+3/10)/(3/2)) := by
  have hp : 0≤(2/3:ℝ)^n := pow_nonneg (by norm_num) n
  have hlo : (3/5:ℝ)≤radius n := by dsimp [radius];nlinarith
  have he : radius (n+1)=(radius n+3/10)/(3/2) := by dsimp [radius];rw [pow_succ];ring
  have hle : radius (n+1)≤radius n := by rw [he];linarith
  exact ⟨hlo,by linarith,he,hle,by rw [min_eq_right (by rw [←he];exact hle),he]⟩

theorem actual_entire_backward_iteration_is_the_computed_interval (n : ℕ) :
    backwardSet n=Icc (-(radius n)) (radius n) := by
  induction n with
  | zero => norm_num [backwardSet,stateConstraint,radius]
  | succ n ih =>
    rw [backwardSet,ih,actual_predecessor_of_every_nonnegative_symmetric_interval
      (radius n) (actual_backward_radius_recurrence_and_geometric_formula n).2.1]
    have he := (actual_backward_radius_recurrence_and_geometric_formula n).2.2.1
    have hle := (actual_backward_radius_recurrence_and_geometric_formula n).2.2.2.1
    ext x
    constructor
    · rintro ⟨hx,hp⟩
      rw [he]
      simpa only [neg_div] using hp
    · intro hx
      refine ⟨?_,?_⟩
      · change -radius n≤x ∧ x≤radius n
        change -radius (n+1)≤x ∧ x≤radius (n+1) at hx
        constructor <;> linarith [hx.1,hx.2]
      · simpa only [he,neg_div] using hx

theorem actual_backward_radii_tend_to_three_fifths :
    Tendsto radius atTop (𝓝 (3/5:ℝ)) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2/3)
    (by norm_num : (2/3:ℝ)<1)).const_mul (2/5)
  change Tendsto (fun n : ℕ=>3/5+(2/5)*(2/3:ℝ)^n) atTop (𝓝 (3/5:ℝ))
  simpa only [mul_zero,add_zero] using tendsto_const_nhds.add h

theorem actual_intersection_of_all_backward_sets_is_the_source_kernel :
    (⋂n,backwardSet n)=Icc (-3/5) (3/5:ℝ) := by
  ext x
  rw [mem_iInter]
  simp only [actual_entire_backward_iteration_is_the_computed_interval,mem_Icc]
  constructor
  · intro h
    have hu : x≤(3/5:ℝ) := ge_of_tendsto actual_backward_radii_tend_to_three_fifths
      (Filter.Eventually.of_forall (fun n=>(h n).2))
    have hl : -x≤(3/5:ℝ) := ge_of_tendsto actual_backward_radii_tend_to_three_fifths
      (Filter.Eventually.of_forall (fun n=>by linarith [(h n).1]))
    constructor <;> linarith
  · rintro ⟨hl,hu⟩ n
    have hb := (actual_backward_radius_recurrence_and_geometric_formula n).1
    constructor <;> linarith

def viableInitials : Set ℝ := {initial | ∃state input : ℕ→ℝ,state 0=initial ∧
  (∀n,input n∈inputConstraint) ∧ (∀n,state (n+1)=nextState (state n) (input n)) ∧
  ∀n,state n∈stateConstraint}

theorem actual_every_admissible_trajectory_has_the_escape_lower_bound
    (state input : ℕ→ℝ) (hinput : ∀n,input n∈inputConstraint)
    (hnext : ∀n,state (n+1)=nextState (state n) (input n)) (n : ℕ) :
    3/5+(3/2:ℝ)^n*(|state 0|-3/5)≤|state n| := by
  have hstep (m : ℕ) : (3/2)*|state m|-3/10≤|state (m+1)| := by
    have hi : |input m|≤(3/10:ℝ) := abs_le.mpr (hinput m)
    have he : (3/2)*state m=state (m+1)-input m := by rw [hnext];dsimp [nextState];ring
    have h := abs_sub (state (m+1)) (input m)
    rw [←he,abs_mul] at h
    norm_num at h
    linarith
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := hstep n
    rw [pow_succ]
    nlinarith

theorem actual_all_time_viability_kernel_is_exactly_the_source_interval :
    viableInitials=Icc (-3/5) (3/5:ℝ) := by
  ext initial
  constructor
  · rintro ⟨state,input,h0,hi,hnext,hs⟩
    have habs : |initial|≤(3/5:ℝ) := by
      by_contra hn
      have hd : 0< |initial|-3/5 := by linarith
      obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt ((2/5)/(|initial|-3/5))
        (by norm_num : (1:ℝ)<3/2)
      have he := actual_every_admissible_trajectory_has_the_escape_lower_bound state input hi hnext n
      rw [h0] at he
      have hb : |state n|≤(1:ℝ) := abs_le.mpr (hs n)
      have hm := mul_lt_mul_of_pos_right hn hd
      have hc : ((2/5)/(|initial|-3/5))*(|initial|-3/5)=(2/5:ℝ) :=
        div_mul_cancel₀ _ hd.ne'
      rw [hc] at hm
      linarith
    constructor <;> linarith [(abs_le.mp habs).1,(abs_le.mp habs).2]
  · intro hi
    refine ⟨fun _=>initial,fun _=>-initial/2,rfl,?_,?_,?_⟩
    · intro n
      change -(3/10:ℝ)≤ -initial/2 ∧ -initial/2≤3/10
      constructor <;> linarith [hi.1,hi.2]
    · intro n;dsimp [nextState];ring
    · intro n
      change (-1:ℝ)≤ initial ∧ initial≤1
      constructor <;> linarith [hi.1,hi.2]

theorem actual_first_backward_radii_and_nearest_three_decimal_displays :
    radius 0=1 ∧ radius 1=13/15 ∧ radius 2=7/9 ∧ radius 3=97/135 ∧
      radius 4=55/81 ∧
    |radius 1-(867/1000:ℝ)|<1/2000 ∧ |radius 2-(778/1000:ℝ)|<1/2000 ∧
    |radius 3-(719/1000:ℝ)|<1/2000 ∧ |radius 4-(679/1000:ℝ)|<1/2000 := by
  norm_num [radius]

end SafeLearning.CompleteAppliedViabilityKernel
