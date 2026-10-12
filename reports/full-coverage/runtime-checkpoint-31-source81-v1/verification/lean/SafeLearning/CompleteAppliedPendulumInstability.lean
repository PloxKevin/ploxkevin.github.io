import SafeLearning.CompleteAppliedPendulumSourceField

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedPendulumInstability
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumSourceField

theorem actual_nonzero_small_upright_initial_angle_has_energy_below_the_saddle
    (q:ℝ) (hq:0<q) (hr:q≤1/10) : physicalEnergy (q,0)<10 := by
  have hp:=Real.pi_gt_three
  have hc : Real.cos q≠1 := by
    intro he
    have hz:=(Real.cos_eq_one_iff_of_lt_of_lt (by linarith : -(2*Real.pi)<q)
      (by linarith : q<2*Real.pi)).mp he
    linarith
  have hl:=lt_of_le_of_ne (Real.cos_le_one q) hc
  dsimp [physicalEnergy]
  nlinarith

theorem actual_upright_small_angle_trajectory_never_crosses_zero
    (q:ℝ) (hq:0<q) (hr:q≤1/10) (t:ℝ) (ht:0≤ t) :
    0<(sourcePath (q,0) t).1 := by
  have he:=actual_nonzero_small_upright_initial_angle_has_energy_below_the_saddle q hq hr
  have hz (s:ℝ) (hs:0≤ s) : (sourcePath (q,0) s).1≠0 := by
    intro heq
    have h:=actual_source_physical_energy_never_increases (q,0) s hs
    dsimp [physicalEnergy] at h
    rw [heq,Real.cos_zero] at h
    dsimp [physicalEnergy] at he
    nlinarith [sq_nonneg ((sourcePath (q,0) s).2)]
  by_contra hp
  have hp' : (sourcePath (q,0) t).1≤0:=le_of_not_gt hp
  have hc:ContinuousOn (fun s=>(sourcePath (q,0) s).1) (Icc 0 t):=
    (actual_source_pendulum_has_a_derived_global_trajectory (q,0)).2.1.fst.continuous.continuousOn
  have hzero:(sourcePath (q,0) 0).1=q:=by
    rw [(actual_source_pendulum_has_a_derived_global_trajectory (q,0)).1]
  obtain ⟨s,hs,hszero⟩:=intermediate_value_Icc' ht hc
    (show (0:ℝ)∈Icc ((sourcePath (q,0) t).1) ((sourcePath (q,0) 0).1) by rw [hzero];exact ⟨hp',hq.le⟩)
  exact hz s hs.1 hszero

theorem actual_positive_small_angle_has_the_needed_nonlinear_acceleration
    (q:ℝ) (hq:0≤ q) (hr:q≤1/10) : q/2≤ Real.sin q := by
  have hs:=Real.sin_ge_sub_cube hq
  have hsq : q^2≤(1/100:ℝ):=by nlinarith
  have hcube:=mul_le_mul_of_nonneg_left hsq hq
  nlinarith

theorem actual_every_small_positive_upright_angle_eventually_leaves_a_fixed_neighborhood
    (q:ℝ) (hq:0<q) (hr:q≤1/10) :
    ∃t:ℝ,0≤ t ∧ (1/10:ℝ)≤‖sourcePath (q,0) t‖ := by
  by_contra hn
  have hsmall (t:ℝ) (ht:0≤ t) : ‖sourcePath (q,0) t‖<(1/10:ℝ) := by
    by_contra h
    exact hn ⟨t,ht,le_of_not_gt h⟩
  have hqsmall (t:ℝ) (ht:0≤ t) : (sourcePath (q,0) t).1≤1/10 := by
    have h:=norm_fst_le (sourcePath (q,0) t)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (hsmall t ht).le)
  have hs (t:ℝ) (ht:0≤ t) : (sourcePath (q,0) t).1/2≤ Real.sin ((sourcePath (q,0) t).1) :=
    actual_positive_small_angle_has_the_needed_nonlinear_acceleration _
      (actual_upright_small_angle_trajectory_never_crosses_zero q hq hr t ht).le (hqsmall t ht)
  have hp:=actual_source_pendulum_has_a_derived_global_trajectory (q,0)
  have hdq (t:ℝ) : HasDerivAt (fun s=>(sourcePath (q,0) s).1) (sourcePath (q,0) t).2 t := by
    have h:=(hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (sourcePath (q,0) t)).comp_hasDerivAt t (hp.2.2.2 t)
    exact h
  have hdv (t:ℝ) : HasDerivAt (fun s=>(sourcePath (q,0) s).2)
      (10*Real.sin ((sourcePath (q,0) t).1)-(sourcePath (q,0) t).2/10) t := by
    have h:=(hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (sourcePath (q,0) t)).comp_hasDerivAt t (hp.2.2.2 t)
    exact h
  have hv (t:ℝ) (ht:0≤ t) : 0≤(sourcePath (q,0) t).2 := by
    have h:=CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
      (fun s=>(sourcePath (q,0) s).2)
      (fun s=>10*Real.sin ((sourcePath (q,0) s).1)-(sourcePath (q,0) s).2/10)
      (1/10) t ht hp.2.1.snd.contDiffOn.absolutelyContinuousOnInterval
      (Eventually.of_forall (fun s _=>hdv s))
      (Eventually.of_forall (fun s hs'=>by
        have hsin:=hs s hs'.1
        have hpos:=actual_upright_small_angle_trajectory_never_crosses_zero q hq hr s hs'.1
        nlinarith)) t ⟨ht,le_rfl⟩
    rw [hp.1] at h
    simpa using h
  have hbound (t:ℝ) (ht:0≤ t) :
      q*Real.exp ((9/10)*t)≤(sourcePath (q,0) t).1+(sourcePath (q,0) t).2 := by
    have h:=CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
      (fun s=>(sourcePath (q,0) s).1+(sourcePath (q,0) s).2)
      (fun s=>(sourcePath (q,0) s).2+
        (10*Real.sin ((sourcePath (q,0) s).1)-(sourcePath (q,0) s).2/10))
      (-9/10) t ht (hp.2.1.fst.add hp.2.1.snd).contDiffOn.absolutelyContinuousOnInterval
      (Eventually.of_forall (fun s _=>(hdq s).add (hdv s)))
      (Eventually.of_forall (fun s hs'=>by
        have hsin:=hs s hs'.1
        have hpos:=actual_upright_small_angle_trajectory_never_crosses_zero q hq hr s hs'.1
        have hvel:=hv s hs'.1
        nlinarith)) t ⟨ht,le_rfl⟩
    rw [hp.1] at h
    convert h using 1 <;> congr 1 <;> ring
  have he : Tendsto (fun t:ℝ=>q*Real.exp ((9/10)*t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<9/10))).const_mul_atTop hq
  obtain ⟨t,ht,hbig⟩:=((eventually_ge_atTop (0:ℝ)).and (he.eventually (eventually_gt_atTop (1:ℝ)))).exists
  have h:=hbound t ht
  have hqnorm:=norm_fst_le (sourcePath (q,0) t)
  have hvnorm:=norm_snd_le (sourcePath (q,0) t)
  rw [Real.norm_eq_abs] at hqnorm hvnorm
  have hsmallt:=hsmall t ht
  nlinarith [le_abs_self ((sourcePath (q,0) t).1),le_abs_self ((sourcePath (q,0) t).2)]

theorem actual_upright_pendulum_is_lyapunov_unstable :
    ∀delta:ℝ,0<delta → ∃initial:ℝ×ℝ,
      ‖initial‖<delta ∧ sourcePath initial 0=initial ∧
      (∀t:ℝ,HasDerivAt (sourcePath initial) (field (sourcePath initial t)) t) ∧
      ∃t:ℝ,0≤ t ∧ (1/10:ℝ)≤‖sourcePath initial t‖ := by
  intro delta hd
  let q:ℝ:=min (delta/2) (1/20)
  have hq:0<q:=lt_min (by positivity) (by norm_num)
  have hr:q≤1/10:=(min_le_right _ _).trans (by norm_num)
  have hqd:q<delta:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨(q,0),?_,(actual_source_pendulum_has_a_derived_global_trajectory (q,0)).1,
    (actual_source_pendulum_has_a_derived_global_trajectory (q,0)).2.2.2,
    actual_every_small_positive_upright_angle_eventually_leaves_a_fixed_neighborhood q hq hr⟩
  simpa [Prod.norm_def,Real.norm_eq_abs,abs_of_pos hq] using (show q<delta ∧ 0<delta from ⟨hqd,hd⟩)

end SafeLearning.CompleteAppliedPendulumInstability
