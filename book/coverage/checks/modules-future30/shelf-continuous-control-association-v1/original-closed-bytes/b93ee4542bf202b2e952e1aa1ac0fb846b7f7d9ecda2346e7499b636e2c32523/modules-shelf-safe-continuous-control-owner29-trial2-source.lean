import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesShelfSafeContinuousControl30

/-- Integral trajectories for the actual safe shelf: three driving speeds,
    safety in [0,L], and the event-driven absorbing wall. -/
structure SafeShelfControl (L v x0 : ℝ) (x u : ℝ → ℝ) : Prop where
  continuous_state : Continuous x
  interval_control : ∀ t, 0 ≤ t → IntervalIntegrable u volume 0 t
  motion : ∀ t, 0 ≤ t → x t = x0 + ∫ s in (0:ℝ)..t, u s
  safe : ∀ t, 0 ≤ t → x t ∈ Icc 0 L
  speeds : ∀ t, 0 ≤ t → u t = -v ∨ u t = 0 ∨ u t = v
  stopped_at_wall : ∀ t, 0 ≤ t → x t = L → u t = 0
  absorbing_wall : ∀ s t, 0 ≤ s → s ≤ t → x s = L → x t = L

def reachTime (L v x0 : ℝ) : ℝ := (L-x0)/v

def rightState (L v x0 t : ℝ) : ℝ := x0 + v * min t (reachTime L v x0)

def rightControl (L v x0 : ℝ) : ℝ → ℝ :=
  (Iio (reachTime L v x0)).indicator (fun _ => v)

def discount (tau t : ℝ) : ℝ := Real.exp (-t/tau)

def discountedReward (L tau : ℝ) (x : ℝ → ℝ) : ℝ → ℝ :=
  {t | x t < L}.indicator (fun t => -discount tau t)

def safeReturn (L tau : ℝ) (x : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), discountedReward L tau x t

def rightReward (L v tau x0 : ℝ) : ℝ → ℝ :=
  (Iio (reachTime L v x0)).indicator (fun t => -discount tau t)

def safeValueFormula (L v tau x0 : ℝ) : ℝ :=
  -tau*(1-Real.exp (-reachTime L v x0/tau))

def safeReturns (L v tau x0 : ℝ) : Set ℝ :=
  {j | ∃ x u, SafeShelfControl L v x0 x u ∧ j = safeReturn L tau x}

def safeOptimalValue (L v tau x0 : ℝ) : ℝ := sSup (safeReturns L v tau x0)

 theorem actual_reach_time_nonnegative {L v x0 : ℝ}
    (hv : 0 < v) (hx : x0 ≤ L) : 0 ≤ reachTime L v x0 :=
  div_nonneg (sub_nonneg.mpr hx) hv.le

 theorem actual_reach_time_identity {L v x0 : ℝ} (hv : 0 < v) :
    v * reachTime L v x0 = L-x0 := by
  unfold reachTime
  field_simp

 theorem actual_control_derives_speed_bound {L v x0 : ℝ} {x u : ℝ → ℝ}
    (hv : 0 < v) (h : SafeShelfControl L v x0 x u) {t : ℝ} (ht : 0 ≤ t) :
    x t ≤ x0 + v*t := by
  rw [h.motion t ht]
  have hm := intervalIntegral.integral_mono_on ht (h.interval_control t ht)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => v) volume 0 t) ?_
  · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
    nlinarith
  · intro s hs
    rcases h.speeds s hs.1 with hs | hs | hs <;> rw [hs] <;> linarith

 theorem actual_no_safe_control_reaches_wall_early {L v x0 : ℝ} {x u : ℝ → ℝ}
    (hv : 0 < v) (h : SafeShelfControl L v x0 x u) {t : ℝ}
    (ht : 0 ≤ t) (hearly : t < reachTime L v x0) : x t < L := by
  have hg := actual_control_derives_speed_bound hv h ht
  have hi := actual_reach_time_identity (L:=L) (x0:=x0) hv
  have hm := mul_lt_mul_of_pos_left hearly hv
  nlinarith

 theorem actual_right_control_interval_integrable (L v x0 a b : ℝ) :
    IntervalIntegrable (rightControl L v x0) volume a b := by
  have hc : IntervalIntegrable (fun _ : ℝ => v) volume a b := intervalIntegrable_const
  exact ⟨hc.1.indicator measurableSet_Iio, hc.2.indicator measurableSet_Iio⟩

 theorem actual_right_control_integral {L v x0 t : ℝ}
    (ha : 0 ≤ reachTime L v x0) (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, rightControl L v x0 s) = v * min t (reachTime L v x0) := by
  let a := reachTime L v x0
  by_cases hta : t ≤ a
  · rw [min_eq_left hta]
    calc
      (∫ s in (0:ℝ)..t, rightControl L v x0 s) = ∫ _ in (0:ℝ)..t, v := by
        apply intervalIntegral.integral_congr_uIoo
        intro s hs
        rw [uIoo_of_le ht] at hs
        simp only [rightControl, indicator_of_mem (show s ∈ Iio (reachTime L v x0) from
          lt_of_lt_of_le hs.2 hta)]
      _ = v*t := by simp [intervalIntegral.integral_const, mul_comm]
  · have hat : a ≤ t := le_of_not_ge hta
    rw [min_eq_right hat]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (actual_right_control_interval_integrable L v x0 0 a)
      (actual_right_control_interval_integrable L v x0 a t)
    have hleft : (∫ s in (0:ℝ)..a, rightControl L v x0 s) = v*a := by
      calc
        (∫ s in (0:ℝ)..a, rightControl L v x0 s) = ∫ _ in (0:ℝ)..a, v := by
          apply intervalIntegral.integral_congr_uIoo
          intro s hs
          rw [uIoo_of_le ha] at hs
          simp only [rightControl, indicator_of_mem (show s ∈ Iio (reachTime L v x0) from hs.2)]
        _ = v*a := by simp [intervalIntegral.integral_const, mul_comm]
    have hright : (∫ s in a..t, rightControl L v x0 s) = 0 := by
      calc
        (∫ s in a..t, rightControl L v x0 s) = ∫ _ in a..t, (0:ℝ) := by
          apply intervalIntegral.integral_congr_uIoo
          intro s hs
          rw [uIoo_of_le hat] at hs
          simp only [rightControl, indicator_of_notMem (show s ∉ Iio (reachTime L v x0) from
            not_lt.mpr hs.1.le)]
        _ = 0 := by simp
    rw [hleft, hright, add_zero] at hsplit
    exact hsplit.symm

 theorem actual_right_state_hits_wall_iff {L v x0 t : ℝ}
    (hv : 0 < v) : rightState L v x0 t = L ↔ reachTime L v x0 ≤ t := by
  have hi := actual_reach_time_identity (L:=L) (x0:=x0) hv
  unfold rightState
  constructor
  · intro he
    by_contra hnot
    have hm : t < reachTime L v x0 := lt_of_not_ge hnot
    rw [min_eq_left hm.le] at he
    have hmul := mul_lt_mul_of_pos_left hm hv
    nlinarith
  · intro ht
    rw [min_eq_right ht]
    linarith

 theorem actual_right_driving_is_safe_control {L v x0 : ℝ}
    (hv : 0 < v) (hx : x0 ∈ Icc 0 L) :
    SafeShelfControl L v x0 (rightState L v x0) (rightControl L v x0) := by
  have ha := actual_reach_time_nonnegative hv hx.2
  have hi := actual_reach_time_identity (L:=L) (x0:=x0) hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rightState
    fun_prop
  · intro t ht
    exact actual_right_control_interval_integrable L v x0 0 t
  · intro t ht
    rw [actual_right_control_integral ha ht]
    rfl
  · intro t ht
    dsimp [rightState]
    have hm : 0 ≤ min t (reachTime L v x0) := le_min ht ha
    have hmul := mul_le_mul_of_nonneg_left (min_le_right t (reachTime L v x0)) hv.le
    constructor
    · exact add_nonneg hx.1 (mul_nonneg hv.le hm)
    · nlinarith
  · intro t ht
    by_cases he : t ∈ Iio (reachTime L v x0)
    · exact Or.inr (Or.inr (indicator_of_mem he _))
    · exact Or.inr (Or.inl (indicator_of_notMem he _))
  · intro t ht he
    have hm := (actual_right_state_hits_wall_iff hv).mp he
    exact indicator_of_notMem (not_lt.mpr hm) _
  · intro s t hs hst he
    exact (actual_right_state_hits_wall_iff hv).mpr
      (((actual_right_state_hits_wall_iff hv).mp he).trans hst)

 theorem actual_right_state_before_wall_iff {L v x0 t : ℝ} (hv : 0 < v) :
    rightState L v x0 t < L ↔ t < reachTime L v x0 := by
  have hi := actual_reach_time_identity (L:=L) (x0:=x0) hv
  unfold rightState
  constructor
  · intro he
    by_contra hn
    rw [min_eq_right (le_of_not_gt hn)] at he
    linarith
  · intro ht
    rw [min_eq_left ht.le]
    have hm := mul_lt_mul_of_pos_left ht hv
    nlinarith

 theorem actual_discount_integrable {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    IntegrableOn (discount tau) (Ioi a) := by
  have hn : (-1:ℝ)/tau < 0 := div_neg_of_neg_of_pos (by norm_num) htau
  convert integrableOn_exp_mul_Ioi hn a using 1
  ext t
  dsimp [discount]
  congr 1
  ring

 theorem actual_discount_tail_integral {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    (∫ t in Ioi a, discount tau t) = tau*Real.exp (-a/tau) := by
  have hn : (-1:ℝ)/tau < 0 := div_neg_of_neg_of_pos (by norm_num) htau
  have he : (fun t : ℝ => Real.exp (((-1:ℝ)/tau)*t)) = discount tau := by
    funext t
    dsimp [discount]
    congr 1
    ring
  rw [←he, integral_exp_mul_Ioi hn]
  have hex : ((-1:ℝ)/tau)*a = -a/tau := by ring
  rw [hex]
  field_simp

 theorem actual_safe_reward_is_the_printed_weighted_reward (L tau : ℝ) (x : ℝ → ℝ) (t : ℝ) :
    discountedReward L tau x t = discount tau t * (if x t < L then (-1:ℝ) else 0) := by
  by_cases hx : x t < L <;> simp [discountedReward, hx]

 theorem actual_safe_reward_integrable {L tau : ℝ} {x : ℝ → ℝ}
    (htau : 0 < tau) (hx : Continuous x) :
    IntegrableOn (discountedReward L tau x) (Ioi (0:ℝ)) := by
  exact ((actual_discount_integrable htau 0).neg).indicator
    (measurableSet_lt hx.measurable measurable_const)

 theorem actual_right_reward_integrable {L v tau x0 : ℝ} (htau : 0 < tau) :
    IntegrableOn (rightReward L v tau x0) (Ioi (0:ℝ)) :=
  ((actual_discount_integrable htau 0).neg).indicator measurableSet_Iio

 theorem actual_right_driving_reward (L v tau x0 : ℝ) (hv : 0 < v) :
    discountedReward L tau (rightState L v x0) = rightReward L v tau x0 := by
  funext t
  have hi := actual_right_state_before_wall_iff (L:=L) (x0:=x0) (t:=t) hv
  by_cases ht : t < reachTime L v x0
  · simp [discountedReward, rightReward, hi.mpr ht, ht]
  · simp [discountedReward, rightReward, not_lt.mpr (le_of_not_gt ht),
      mt hi.mp ht]

 theorem actual_infinite_right_driving_return {L v tau x0 : ℝ}
    (htau : 0 < tau) (ha : 0 ≤ reachTime L v x0) :
    (∫ t in Ioi (0:ℝ), rightReward L v tau x0 t) = safeValueFormula L v tau x0 := by
  let a := reachTime L v x0
  have hdiff := intervalIntegral.integral_Ioi_sub_Ioi (actual_discount_integrable htau 0) ha
  have hbase := actual_discount_tail_integral htau 0
  have htail := actual_discount_tail_integral htau a
  calc
    (∫ t in Ioi (0:ℝ), rightReward L v tau x0 t) =
        ∫ t in Ioo (0:ℝ) a, -discount tau t := by
      unfold rightReward
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        Iio_inter_Ioi]
    _ = -(∫ t in (0:ℝ)..a, discount tau t) := by
      rw [integral_neg, intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
    _ = safeValueFormula L v tau x0 := by
      rw [←hdiff, hbase, htail]
      simp only [zero_div, neg_zero, Real.exp_zero, mul_one]
      dsimp [safeValueFormula]
      ring

 theorem actual_every_safe_controller_return_upper_bound {L v tau x0 : ℝ} {x u : ℝ → ℝ}
    (hv : 0 < v) (htau : 0 < tau) (hx : x0 ∈ Icc 0 L)
    (h : SafeShelfControl L v x0 x u) :
    safeReturn L tau x ≤ safeValueFormula L v tau x0 := by
  rw [←actual_infinite_right_driving_return htau (actual_reach_time_nonnegative hv hx.2)]
  apply integral_mono_ae (actual_safe_reward_integrable htau h.continuous_state)
    (actual_right_reward_integrable htau)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  exact Filter.Eventually.of_forall fun t ht => by
    by_cases hearly : t < reachTime L v x0
    · have hlt := actual_no_safe_control_reaches_wall_early hv h ht.le hearly
      simp [discountedReward, rightReward, hearly, hlt]
    · have hnot : t ∉ Iio (reachTime L v x0) := hearly
      rw [rightReward, indicator_of_notMem hnot]
      by_cases hlt : x t < L
      · simp [discountedReward, hlt, discount, (Real.exp_pos _).le]
      · simp [discountedReward, hlt]

 theorem actual_safe_optimum_is_attained_by_right_driving {L v tau x0 : ℝ}
    (hv : 0 < v) (htau : 0 < tau) (hx : x0 ∈ Icc 0 L) :
    IsGreatest (safeReturns L v tau x0) (safeValueFormula L v tau x0) := by
  constructor
  · refine ⟨rightState L v x0, rightControl L v x0, actual_right_driving_is_safe_control hv hx, ?_⟩
    unfold safeReturn
    rw [actual_right_driving_reward L v tau x0 hv,
      actual_infinite_right_driving_return htau (actual_reach_time_nonnegative hv hx.2)]
  · intro j hj
    rcases hj with ⟨x,u,h,rfl⟩
    exact actual_every_safe_controller_return_upper_bound hv htau hx h

 theorem actual_constrained_value_from_continuous_controls {L v tau x0 : ℝ}
    (hv : 0 < v) (htau : 0 < tau) (hx : x0 ∈ Icc 0 L) :
    safeOptimalValue L v tau x0 = safeValueFormula L v tau x0 :=
  (actual_safe_optimum_is_attained_by_right_driving hv htau hx).csSup_eq

 theorem actual_ledge_attains_constrained_value_infimum {L v tau : ℝ}
    (hL : 0 ≤ L) (hv : 0 < v) (htau : 0 < tau) :
    IsLeast (safeOptimalValue L v tau '' Icc (0:ℝ) L) (safeValueFormula L v tau 0) := by
  constructor
  · refine ⟨0, ⟨le_rfl,hL⟩, ?_⟩
    exact actual_constrained_value_from_continuous_controls hv htau ⟨le_rfl,hL⟩
  · intro y hy
    rcases hy with ⟨x0,hx,rfl⟩
    rw [actual_constrained_value_from_continuous_controls hv htau hx]
    have ha : reachTime L v x0 ≤ reachTime L v 0 := by
      unfold reachTime
      exact div_le_div_of_nonneg_right (by linarith [hx.1]) hv.le
    have hb : -reachTime L v 0/tau ≤ -reachTime L v x0/tau :=
      div_le_div_of_nonneg_right (neg_le_neg ha) htau.le
    have he := Real.exp_le_exp.mpr hb
    dsimp [safeValueFormula]
    nlinarith

 theorem actual_default_ledge_infimum_is_printed_formula {tau : ℝ} (htau : 0 < tau) :
    sInf (safeOptimalValue 1 (1/5) tau '' Icc (0:ℝ) 1) =
      -tau*(1-Real.exp (-5/tau)) := by
  rw [(actual_ledge_attains_constrained_value_infimum (L:=1) (v:=1/5)
    (by norm_num) (by norm_num) htau).csInf_eq]
  norm_num [safeValueFormula, reachTime]

end SafeLearning.CompleteModulesShelfSafeContinuousControl30
