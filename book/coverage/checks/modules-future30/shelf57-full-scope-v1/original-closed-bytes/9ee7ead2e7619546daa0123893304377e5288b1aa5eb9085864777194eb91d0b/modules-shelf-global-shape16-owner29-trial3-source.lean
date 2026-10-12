import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Topology
open Filter Set
namespace SafeLearning.CompleteModulesShelfGlobalShape30

def shelfThreshold (a b tau : ℝ) : ℝ :=
  tau * (2 - Real.exp (-a/tau)) * Real.exp (b/tau) - tau

theorem actual_shelf_threshold_equivalent_form (a b tau : ℝ) :
    shelfThreshold a b tau =
      tau * (2*Real.exp (b/tau) - Real.exp ((b-a)/tau) - 1) := by
  have he : Real.exp (-a/tau) * Real.exp (b/tau) = Real.exp ((b-a)/tau) := by
    rw [←Real.exp_add]; congr 1; ring
  unfold shelfThreshold
  rw [←he]
  ring

def shelfDerivativeProfile (x : ℝ) : ℝ :=
  2*Real.exp x*(1-x)-Real.exp (-4*x)*(1+4*x)-1

def derivativeTurningPoint : ℝ := Real.log 8/5

theorem actual_shelf_profile_derivative (x : ℝ) :
    HasDerivAt shelfDerivativeProfile
      (x*(16*Real.exp (-4*x)-2*Real.exp x)) x := by
  have h1 := ((Real.hasDerivAt_exp x).const_mul 2).mul
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
  have h2 := (((hasDerivAt_id x).const_mul (-4)).exp).mul
    ((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul 4))
  convert (h1.sub h2).sub (hasDerivAt_const x 1) using 1
  · funext t
    dsimp [shelfDerivativeProfile]
    ring
  · dsimp
    ring

theorem actual_shelf_profile_continuous : Continuous shelfDerivativeProfile := by
  unfold shelfDerivativeProfile
  fun_prop

theorem actual_turning_point_is_between_zero_and_one :
    0 < derivativeTurningPoint ∧ derivativeTurningPoint < 1 := by
  have hl : 0 < Real.log (8:ℝ) := Real.log_pos (by norm_num)
  have h2 : (3:ℝ) < Real.exp 2 := by
    convert Real.add_one_lt_exp (by norm_num : (2:ℝ) ≠ 0) using 1 <;> norm_num
  have h4 : (9:ℝ) < Real.exp 4 := by
    rw [show (4:ℝ)=2+2 by ring, Real.exp_add]
    nlinarith [Real.exp_pos 2]
  have h5 : (8:ℝ) < Real.exp 5 := by
    have hm := Real.exp_lt_exp.mpr (show (4:ℝ)<5 by norm_num)
    linarith
  have hlog : Real.log (8:ℝ) < 5 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr h5
  unfold derivativeTurningPoint
  constructor <;> linarith

theorem actual_shelf_profile_derivative_factorization (x : ℝ) :
    x*(16*Real.exp (-4*x)-2*Real.exp x) =
      2*x*Real.exp (-4*x)*(8-Real.exp (5*x)) := by
  have he : Real.exp (-4*x)*Real.exp (5*x)=Real.exp x := by
    rw [←Real.exp_add]; congr 1; ring
  rw [←he]
  ring

theorem actual_shelf_profile_rises_until_turning_point :
    StrictMonoOn shelfDerivativeProfile (Icc 0 derivativeTurningPoint) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 derivativeTurningPoint) actual_shelf_profile_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(actual_shelf_profile_derivative x).deriv, actual_shelf_profile_derivative_factorization]
  apply mul_pos (mul_pos (mul_pos (by norm_num) hx.1) (Real.exp_pos _))
  apply sub_pos.mpr
  have hxlog : 5*x < Real.log (8:ℝ) := by
    dsimp [derivativeTurningPoint] at hx
    linarith [hx.2]
  have he := Real.exp_lt_exp.mpr hxlog
  rwa [Real.exp_log (by norm_num : (0:ℝ)<8)] at he

theorem actual_shelf_profile_falls_after_turning_point :
    StrictAntiOn shelfDerivativeProfile (Ici derivativeTurningPoint) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici derivativeTurningPoint) actual_shelf_profile_continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change derivativeTurningPoint<x at hx
  rw [(actual_shelf_profile_derivative x).deriv, actual_shelf_profile_derivative_factorization]
  have hc := actual_turning_point_is_between_zero_and_one
  have hxpos : 0 < x := lt_trans hc.1 hx
  apply mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hxpos) (Real.exp_pos _))
  apply sub_neg.mpr
  have hxlog : Real.log (8:ℝ) < 5*x := by
    dsimp [derivativeTurningPoint] at hx
    linarith
  have he := Real.exp_lt_exp.mpr hxlog
  rwa [Real.exp_log (by norm_num : (0:ℝ)<8)] at he

theorem actual_shelf_profile_zero_and_endpoint_signs :
    shelfDerivativeProfile 0=0 ∧
    0 < shelfDerivativeProfile derivativeTurningPoint ∧
    shelfDerivativeProfile 1 < 0 := by
  have h0 : shelfDerivativeProfile 0=0 := by norm_num [shelfDerivativeProfile]
  have hc := actual_turning_point_is_between_zero_and_one
  have hp := actual_shelf_profile_rises_until_turning_point
    (show (0:ℝ)∈Icc 0 derivativeTurningPoint from ⟨le_rfl,hc.1.le⟩)
    (show derivativeTurningPoint∈Icc 0 derivativeTurningPoint from ⟨hc.1.le,le_rfl⟩) hc.1
  refine ⟨h0,by simpa only [h0] using hp,?_⟩
  norm_num [shelfDerivativeProfile]
  linarith [Real.exp_pos (-4)]

theorem actual_shelf_positive_profile_root_exists_uniquely :
    ∃ r : ℝ, r∈Ioo derivativeTurningPoint 1 ∧ shelfDerivativeProfile r=0 ∧
      (∀ x : ℝ, 0<x → x<r → 0<shelfDerivativeProfile x) ∧
      (∀ x : ℝ, r<x → shelfDerivativeProfile x<0) := by
  have hc := actual_turning_point_is_between_zero_and_one
  have hs := actual_shelf_profile_zero_and_endpoint_signs
  obtain ⟨r,hr,her⟩ := intermediate_value_Icc' hc.2.le
    actual_shelf_profile_continuous.continuousOn
    (show (0:ℝ)∈Icc (shelfDerivativeProfile 1) (shelfDerivativeProfile derivativeTurningPoint)
      from ⟨hs.2.2.le,hs.2.1.le⟩)
  have hrc : derivativeTurningPoint<r := by
    by_contra hn
    have heq : r=derivativeTurningPoint := le_antisymm (le_of_not_gt hn) hr.1
    subst r
    linarith [hs.2.1]
  have hr1 : r<1 := by
    by_contra hn
    have heq : r=1 := le_antisymm hr.2 (le_of_not_gt hn)
    subst r
    linarith [hs.2.2]
  refine ⟨r,⟨hrc,hr1⟩,her,?_,?_⟩
  · intro x hx hxr
    by_cases hxc : x≤derivativeTurningPoint
    · have h := actual_shelf_profile_rises_until_turning_point
        (show (0:ℝ)∈Icc 0 derivativeTurningPoint from ⟨le_rfl,hc.1.le⟩)
        (show x∈Icc 0 derivativeTurningPoint from ⟨hx.le,hxc⟩) hx
      simpa only [hs.1] using h
    · have h := actual_shelf_profile_falls_after_turning_point
        (show x∈Ici derivativeTurningPoint from le_of_not_ge hxc)
        (show r∈Ici derivativeTurningPoint from hrc.le) hxr
      simpa only [her] using h
  · intro x hrx
    have h := actual_shelf_profile_falls_after_turning_point
      (show r∈Ici derivativeTurningPoint from hrc.le)
      (show x∈Ici derivativeTurningPoint from le_trans hrc.le hrx.le) hrx
    simpa only [her] using h

theorem actual_shelf_tau_derivative (tau : ℝ) (ht : 0<tau) :
    HasDerivAt (shelfThreshold 5 1) (shelfDerivativeProfile (1/tau)) tau := by
  have hn := ne_of_gt ht
  have h1 := ((hasDerivAt_const tau 1).div (hasDerivAt_id tau) hn).exp
  have h2 := ((hasDerivAt_const tau (-4)).div (hasDerivAt_id tau) hn).exp
  have h := (hasDerivAt_id tau).mul
    (((h1.const_mul 2).sub h2).sub (hasDerivAt_const tau 1))
  convert h using 1
  · funext t
    rw [actual_shelf_threshold_equivalent_form]
    norm_num
  · dsimp [shelfDerivativeProfile]
    field_simp
    ring

theorem actual_shelf_has_unique_global_minimum_and_decrease_then_increase :
    ∃ tauStar : ℝ, 0<tauStar ∧
      StrictAntiOn (shelfThreshold 5 1) (Ioc 0 tauStar) ∧
      StrictMonoOn (shelfThreshold 5 1) (Ici tauStar) ∧
      (∀ tau : ℝ, 0<tau → tau≠tauStar →
        shelfThreshold 5 1 tauStar < shelfThreshold 5 1 tau) := by
  obtain ⟨r,hr,her,hpositive,hnegative⟩ := actual_shelf_positive_profile_root_exists_uniquely
  have hc := actual_turning_point_is_between_zero_and_one
  have hrpos : 0<r := lt_trans hc.1 hr.1
  let tauStar : ℝ := 1/r
  have hstar : 0<tauStar := one_div_pos.mpr hrpos
  have hanti : StrictAntiOn (shelfThreshold 5 1) (Ioc 0 tauStar) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 tauStar)
    · intro t ht
      exact (actual_shelf_tau_derivative t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(actual_shelf_tau_derivative t ht.1).deriv]
      apply hnegative
      have hlt : t*r<1 := (lt_div_iff₀ hrpos).mp ht.2
      exact (lt_div_iff₀ ht.1).mpr (by nlinarith)
  have hmono : StrictMonoOn (shelfThreshold 5 1) (Ici tauStar) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici tauStar)
    · intro t ht
      exact (actual_shelf_tau_derivative t (lt_of_lt_of_le hstar ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change tauStar<t at ht
      have htpos : 0<t := lt_trans hstar ht
      rw [(actual_shelf_tau_derivative t htpos).deriv]
      apply hpositive _ (one_div_pos.mpr htpos)
      have hlt : 1<t*r := (div_lt_iff₀ hrpos).mp ht
      exact (div_lt_iff₀ htpos).mpr (by nlinarith)
  refine ⟨tauStar,hstar,hanti,hmono,?_⟩
  intro tau ht hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact hanti ⟨ht,hlt.le⟩ ⟨hstar,le_rfl⟩ hlt
  · exact hmono (by simp only [Set.mem_Ici]; exact le_rfl) hgt.le hgt

end SafeLearning.CompleteModulesShelfGlobalShape30

namespace SafeLearning.CompleteModulesShelfGlobalShape30

def constrainedLedgeValue (tau : ℝ) : ℝ :=
  -tau*(1-Real.exp (-5/tau))

theorem actual_constrained_ledge_value_derivative (tau : ℝ) (ht : 0<tau) :
    HasDerivAt constrainedLedgeValue
      (-1+Real.exp (-5/tau)*(1+5/tau)) tau := by
  have he := ((hasDerivAt_const tau (-5)).div (hasDerivAt_id tau) (ne_of_gt ht)).exp
  have h := ((hasDerivAt_id tau).neg).mul ((hasDerivAt_const tau 1).sub he)
  convert h using 1
  · rfl
  · field_simp
    ring

theorem actual_constrained_ledge_value_strictly_decreases :
    StrictAntiOn constrainedLedgeValue (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro tau ht
    exact (actual_constrained_ledge_value_derivative tau ht).continuousAt.continuousWithinAt
  · intro tau ht
    rw [interior_Ioi] at ht
    change 0<tau at ht
    rw [(actual_constrained_ledge_value_derivative tau ht).deriv]
    have hx : 0<(5:ℝ)/tau := div_pos (by norm_num) ht
    have hb := Real.add_one_lt_exp (ne_of_gt hx)
    have hp := mul_lt_mul_of_pos_left hb (Real.exp_pos (-(5:ℝ)/tau))
    have he : Real.exp (-(5:ℝ)/tau)*Real.exp (5/tau)=1 := by
      rw [←Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [he] at hp
    linarith

theorem actual_constrained_ledge_value_limit_error (tau : ℝ) (ht : 5≤tau) :
    |constrainedLedgeValue tau-(-5)| ≤ 41/tau := by
  have hpos : 0<tau := by linarith
  have hn := ne_of_gt hpos
  have hx : |(-5:ℝ)/tau|≤1 := by
    rw [abs_div,abs_of_pos hpos]
    norm_num
    exact (div_le_one hpos).mpr ht
  let r := Real.exp (-5/tau)-(1-5/tau+(-5/tau)^2/2)
  have hb : |r|≤(2/9:ℝ)*(5/tau)^3 := by
    have h := Real.exp_bound hx (n:=3) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    convert h using 1 <;> dsimp [r] <;> rw [abs_div,abs_of_pos hpos] <;> norm_num <;> ring
  have hid : constrainedLedgeValue tau-(-5)=25/(2*tau)+tau*r := by
    dsimp [constrainedLedgeValue,r]
    field_simp
    ring
  have hcubic : tau*((2/9:ℝ)*(5/tau)^3)≤28/tau := by
    have heq : tau*((2/9:ℝ)*(5/tau)^3)=(250/9:ℝ)/tau^2 := by field_simp; ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hpos).mpr
    have h := mul_le_mul_of_nonneg_left (show (250/9:ℝ)≤28*tau by linarith) hpos.le
    nlinarith
  calc
    |constrainedLedgeValue tau-(-5)|=|25/(2*tau)+tau*r| := congrArg abs hid
    _ ≤ |25/(2*tau)|+|tau*r| := abs_add_le _ _
    _ = 25/(2*tau)+tau*|r| := by
      rw [abs_mul,abs_of_pos hpos,abs_of_pos (div_pos (by norm_num) (by positivity))]
    _ ≤ 25/(2*tau)+tau*((2/9:ℝ)*(5/tau)^3) := by gcongr
    _ ≤ 25/(2*tau)+28/tau := add_le_add le_rfl hcubic
    _ ≤ 41/tau := by field_simp; nlinarith

theorem actual_constrained_ledge_value_tends_to_negative_five :
    Tendsto constrainedLedgeValue atTop (𝓝 (-5)) := by
  refine Metric.tendsto_atTop.mpr (fun eps heps => ?_)
  refine ⟨max 5 (41/eps+1),fun tau htau => ?_⟩
  have h5 : 5≤tau := le_trans (le_max_left _ _) htau
  have ht : 0<tau := by linarith
  have he : 41/eps<tau := by linarith [le_trans (le_max_right _ _) htau]
  have hsmall : 41/tau<eps := (div_lt_iff₀ ht).mpr (by
    have h := (div_lt_iff₀ heps).mp he
    nlinarith)
  simpa only [Real.dist_eq] using (actual_constrained_ledge_value_limit_error tau h5).trans_lt hsmall

end SafeLearning.CompleteModulesShelfGlobalShape30
