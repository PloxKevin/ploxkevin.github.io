import SafeLearning.CompleteAppliedNonlinearEquilibria

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedNonlinearLocalStability
open CompleteAppliedNonlinearEquilibria

def actualSolution (initial time : ℝ) : ℝ :=
  initial/(initial+(1-initial)*Real.exp time)

theorem actual_forward_denominator_is_at_least_one (initial time : ℝ)
    (hi : initial ≤ 1) (ht : 0 ≤ time) :
    1 ≤ initial+(1-initial)*Real.exp time := by
  have he : 1 ≤ Real.exp time := by simpa using Real.exp_le_exp.mpr ht
  have hm := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hi)
  nlinarith

theorem actual_initial_condition (initial : ℝ) : actualSolution initial 0=initial := by
  simp [actualSolution]

theorem actual_solution_has_the_true_nonlinear_ODE (initial time : ℝ)
    (hden : initial+(1-initial)*Real.exp time≠0) :
    HasDerivAt (actualSolution initial) (field (actualSolution initial time)) time := by
  have hd := ((Real.hasDerivAt_exp time).const_mul (1-initial)).const_add initial
  convert (hasDerivAt_const time initial).div hd hden using 1
  · rfl
  · dsimp [field,actualSolution]
    field_simp
    ring

theorem actual_every_initial_below_one_has_a_forward_global_solution (initial : ℝ)
    (hi : initial<1) :
    actualSolution initial 0=initial ∧ ContinuousOn (actualSolution initial) (Ici 0) ∧
      ∀time:ℝ,0≤time→HasDerivAt (actualSolution initial)
        (field (actualSolution initial time)) time := by
  have hd : ∀time:ℝ,0≤time→HasDerivAt (actualSolution initial)
      (field (actualSolution initial time)) time := by
    intro time ht
    apply actual_solution_has_the_true_nonlinear_ODE
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      (actual_forward_denominator_is_at_least_one initial time hi.le ht))
  refine ⟨actual_initial_condition initial,?_,hd⟩
  intro time ht
  exact (hd time ht).continuousAt.continuousWithinAt

theorem actual_all_below_one_initial_solutions_tend_to_zero (initial : ℝ)
    (hi : initial<1) : Tendsto (actualSolution initial) atTop (𝓝 0) := by
  have hden : Tendsto (fun time:ℝ=>initial+(1-initial)*Real.exp time) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_exp_atTop.const_mul_atTop (sub_pos.mpr hi))
  change Tendsto (fun time:ℝ=>initial/(initial+(1-initial)*Real.exp time)) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop hden

/-- Compactness bounds the actual varying coefficient in the difference ODE;
no solution value, range or uniqueness is supplied as a premise. -/
theorem actual_classical_nonlinear_ODE_solutions_are_unique_on_every_finite_interval
    (x y : ℝ→ℝ) (horizon : ℝ)
    (hxc : ContinuousOn x (Icc 0 horizon)) (hyc : ContinuousOn y (Icc 0 horizon))
    (hxd : ∀time∈Ico 0 horizon,HasDerivAt x (field (x time)) time)
    (hyd : ∀time∈Ico 0 horizon,HasDerivAt y (field (y time)) time)
    (hinitial : x 0=y 0) : ∀time∈Icc 0 horizon,x time=y time := by
  have hcoef : ContinuousOn (fun time:ℝ=>|-1+x time+y time|) (Icc 0 horizon) :=
    ((continuousOn_const.add hxc).add hyc).abs
  obtain ⟨K,hK⟩ := isCompact_Icc.bddAbove_image hcoef
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f:=fun time:ℝ=>x time-y time)
    (f':=fun time:ℝ=>field (x time)-field (y time)) (K:=K)
    (hxc.sub hyc) (fun time ht=>(hxd time ht).sub (hyd time ht) |>.hasDerivWithinAt)
    (by simp [hinitial]) ?_
  · intro time ht
    exact sub_eq_zero.mp (hzero time ht)
  · intro time ht
    have hk : |-1+x time+y time|≤K := hK ⟨time,Ico_subset_Icc_self ht,rfl⟩
    rw [show field (x time)-field (y time)=(-1+x time+y time)*(x time-y time) by
      dsimp [field];ring]
    simpa only [Real.norm_eq_abs,abs_mul] using
      mul_le_mul_of_nonneg_right hk (abs_nonneg (x time-y time))

theorem actual_every_below_one_initial_classical_trajectory_equals_the_solution
    (x : ℝ→ℝ) (initial horizon : ℝ) (hi : initial<1)
    (hc : ContinuousOn x (Icc 0 horizon)) (hx0 : x 0=initial)
    (hd : ∀time∈Ico 0 horizon,HasDerivAt x (field (x time)) time) :
    ∀time∈Icc 0 horizon,x time=actualSolution initial time := by
  have hs := actual_every_initial_below_one_has_a_forward_global_solution initial hi
  exact actual_classical_nonlinear_ODE_solutions_are_unique_on_every_finite_interval
    x (actualSolution initial) horizon hc (hs.2.1.mono Icc_subset_Ici_self)
    hd (fun time ht=>hs.2.2 time ht.1) (hx0.trans hs.1.symm)

theorem actual_forward_solution_magnitude_does_not_exceed_initial_magnitude
    (initial time : ℝ) (hi : initial≤1) (ht : 0≤time) :
    |actualSolution initial time|≤|initial| := by
  have hden := actual_forward_denominator_is_at_least_one initial time hi ht
  rw [actualSolution,abs_div,abs_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hden)]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hden)).mpr
    (by nlinarith [abs_nonneg initial])

def locallyStable (equilibrium : ℝ) : Prop :=
  ∀epsilon:ℝ,0<epsilon→∃delta:ℝ,0<delta ∧
    ∀initial horizon:ℝ,|initial-equilibrium|<delta→
    ∀x:ℝ→ℝ,ContinuousOn x (Icc 0 horizon)→x 0=initial→
      (∀time∈Ico 0 horizon,HasDerivAt x (field (x time)) time)→
      ∀time∈Icc 0 horizon,|x time-equilibrium|<epsilon

def locallyAttractive (equilibrium : ℝ) : Prop :=
  ∃delta:ℝ,0<delta ∧ ∀initial:ℝ,|initial-equilibrium|<delta→
    ∀x:ℝ→ℝ,ContinuousOn x (Ici 0)→x 0=initial→
      (∀time:ℝ,0≤time→HasDerivAt x (field (x time)) time)→
      Tendsto x atTop (𝓝 equilibrium)

theorem actual_zero_equilibrium_is_locally_stable : locallyStable 0 := by
  intro epsilon he
  refine ⟨min epsilon (1/2),lt_min he (by norm_num),?_⟩
  intro initial horizon hi x hc hx0 hd time ht
  have hab : |initial| < min epsilon (1/2) := by simpa using hi
  have hismall : |initial|<(1/2:ℝ) := hab.trans_le (min_le_right _ _)
  have hil : initial<1 := by linarith [le_abs_self initial]
  rw [actual_every_below_one_initial_classical_trajectory_equals_the_solution
    x initial horizon hil hc hx0 hd time ht,sub_zero]
  exact (actual_forward_solution_magnitude_does_not_exceed_initial_magnitude
    initial time hil.le ht.1).trans_lt (hab.trans_le (min_le_left _ _))

theorem actual_zero_equilibrium_is_locally_attractive : locallyAttractive 0 := by
  refine ⟨1/2,by norm_num,?_⟩
  intro initial hi x hc hx0 hd
  have hismall : |initial|<(1/2:ℝ) := by simpa using hi
  have hil : initial<1 := by linarith [le_abs_self initial]
  have heq : x=ᶠ[atTop]actualSolution initial := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with time ht
    exact actual_every_below_one_initial_classical_trajectory_equals_the_solution
      x initial time hil (hc.mono Icc_subset_Ici_self) hx0
      (fun s hs=>hd s hs.1) time ⟨ht,le_rfl⟩
  exact (actual_all_below_one_initial_solutions_tend_to_zero initial hil).congr' heq.symm

theorem actual_one_equilibrium_is_unstable : ¬locallyStable 1 := by
  intro hstable
  obtain ⟨delta,hd,h⟩ := hstable (1/2) (by norm_num)
  let a : ℝ := min (delta/2) (1/4)
  have ha : 0<a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have hadelta : a<delta := by dsimp [a];exact (min_le_left _ _).trans_lt (by linarith)
  have haquarter : a≤1/4 := min_le_right _ _
  let initial : ℝ := 1-a
  have hi : initial<1 := by dsimp [initial];linarith
  have hsmall : |initial-1|<delta := by
    rw [show initial-1= -a by dsimp [initial];ring,abs_neg,abs_of_pos ha]
    exact hadelta
  have hs := actual_every_initial_below_one_has_a_forward_global_solution initial hi
  have htend := actual_all_below_one_initial_solutions_tend_to_zero initial hi
  obtain ⟨time,ht,hvalue⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (htend.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))).exists
  have hnear := h initial time hsmall (actualSolution initial)
    (hs.2.1.mono Icc_subset_Ici_self) hs.1 (fun s hs'=>hs.2.2 s hs'.1)
    time ⟨ht,le_rfl⟩
  have hleft := (abs_lt.mp hnear).1
  linarith

end SafeLearning.CompleteAppliedNonlinearLocalStability
