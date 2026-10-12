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
  · dsimp
    field_simp
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

private theorem actual_exp_quadratic_remainder_bound (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - (1+x+x^2/2)| ≤ (2/9:ℝ)*|x|^3 := by
  have h := Real.exp_bound hx (n:=3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  convert h using 1 <;> ring

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
    have h := actual_exp_quadratic_remainder_bound (-5/tau) hx
    norm_num [abs_div,abs_of_pos hpos] at h
    simpa only [r,sub_eq_add_neg,neg_div] using h
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

namespace SafeLearning.CompleteModulesShelfGlobalShape30

theorem actual_exp_minimum_lo_positive_rational_enclosure :
    (1991794/1000000:ℝ) ≤ Real.exp (10000/14513:ℝ) ∧
    Real.exp (10000/14513:ℝ) ≤ (1991798/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(10000/14513:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_minimum_hi_positive_rational_enclosure :
    (1991983/1000000:ℝ) ≤ Real.exp (10000/14511:ℝ) ∧
    Real.exp (10000/14511:ℝ) ≤ (1991987/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(10000/14511:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_minimum_lo_negative_rational_enclosure :
    (502056/1000000:ℝ) ≤ Real.exp (-10000/14513:ℝ) ∧
    Real.exp (-10000/14513:ℝ) ≤ (502060/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-10000/14513:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_exp_minimum_hi_negative_rational_enclosure :
    (502008/1000000:ℝ) ≤ Real.exp (-10000/14511:ℝ) ∧
    Real.exp (-10000/14511:ℝ) ≤ (502012/1000000:ℝ) := by
  have h := abs_le.mp (Real.exp_bound (x:=(-10000/14511:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

private theorem actual_exp_fourfold_enclosure (x lo hi : ℝ) (hlo : 0≤lo)
    (hb : lo≤Real.exp x ∧ Real.exp x≤hi) :
    lo^4≤Real.exp (4*x) ∧ Real.exp (4*x)≤hi^4 := by
  rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.exp_nat_mul]
  constructor
  · gcongr
    exact hb.1
  · gcongr
    exact hb.2

theorem actual_shelf_turning_point_less_than_three_fifths :
    derivativeTurningPoint < (3/5:ℝ) := by
  have h1 : (2:ℝ)<Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    norm_num at h
    exact h
  have h3 : (8:ℝ)<Real.exp 3 := by
    rw [show (3:ℝ)=(3:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    have hp : 0<(Real.exp 1-2)*((Real.exp 1)^2+2*Real.exp 1+4) :=
      mul_pos (by linarith) (by nlinarith [Real.exp_pos 1])
    nlinarith
  have hlog := (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<8)).mpr h3
  dsimp [derivativeTurningPoint]
  linarith

theorem actual_shelf_profile_numeric_endpoint_signs :
    0<shelfDerivativeProfile (10000/14513) ∧
    shelfDerivativeProfile (10000/14511)<0 := by
  have l1 := actual_exp_minimum_lo_positive_rational_enclosure
  have l2 := actual_exp_fourfold_enclosure (-10000/14513) (502056/1000000) (502060/1000000)
    (by norm_num) actual_exp_minimum_lo_negative_rational_enclosure
  have h1 := actual_exp_minimum_hi_positive_rational_enclosure
  have h2 := actual_exp_fourfold_enclosure (-10000/14511) (502008/1000000) (502012/1000000)
    (by norm_num) actual_exp_minimum_hi_negative_rational_enclosure
  norm_num at l1 l2 h1 h2
  constructor <;> dsimp [shelfDerivativeProfile] <;> norm_num <;>
    linarith [l1.1,l1.2,l2.1,l2.2,h1.1,h1.2,h2.1,h2.2]

theorem actual_shelf_profile_root_has_exact_small_interval
    (r : ℝ) (hr : r∈Ioo derivativeTurningPoint 1) (her : shelfDerivativeProfile r=0) :
    (10000/14513:ℝ)<r ∧ r<(10000/14511:ℝ) := by
  have hs := actual_shelf_profile_numeric_endpoint_signs
  have hc := actual_shelf_turning_point_less_than_three_fifths
  have hl : derivativeTurningPoint<(10000/14513:ℝ) := by linarith
  have hh : derivativeTurningPoint<(10000/14511:ℝ) := by linarith
  constructor
  · by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with h|h
    · have hd := actual_shelf_profile_falls_after_turning_point hr.1.le hl.le h
      rw [her] at hd
      linarith [hs.1]
    · rw [h] at her
      linarith [hs.1]
  · by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with h|h
    · have hd := actual_shelf_profile_falls_after_turning_point hh.le hr.1.le h
      rw [her] at hd
      linarith [hs.2]
    · rw [←h] at her
      linarith [hs.2]

theorem actual_shelf_minimum_location_and_value_rounding
    (r : ℝ) (hr : r∈Ioo derivativeTurningPoint 1) (her : shelfDerivativeProfile r=0) :
    (14511/10000:ℝ)<1/r ∧ 1/r<(14513/10000:ℝ) ∧
    (847/200:ℝ)<shelfThreshold 5 1 (1/r) ∧
    shelfThreshold 5 1 (1/r)<(849/200:ℝ) := by
  have hb := actual_shelf_profile_root_has_exact_small_interval r hr her
  have hrpos : 0<r := by linarith [hb.1]
  have htl : (14511/10000:ℝ)<1/r := (lt_div_iff₀ hrpos).mpr (by linarith [hb.2])
  have hth : 1/r<(14513/10000:ℝ) := (div_lt_iff₀ hrpos).mpr (by linarith [hb.1])
  have epl : (1991794/1000000:ℝ)≤Real.exp r :=
    actual_exp_minimum_lo_positive_rational_enclosure.1.trans (Real.exp_le_exp.mpr hb.1.le)
  have eph : Real.exp r≤(1991987/1000000:ℝ) :=
    (Real.exp_le_exp.mpr hb.2.le).trans actual_exp_minimum_hi_positive_rational_enclosure.2
  have ennl := actual_exp_fourfold_enclosure (-10000/14511) (502008/1000000) (502012/1000000)
    (by norm_num) actual_exp_minimum_hi_negative_rational_enclosure
  have ennh := actual_exp_fourfold_enclosure (-10000/14513) (502056/1000000) (502060/1000000)
    (by norm_num) actual_exp_minimum_lo_negative_rational_enclosure
  have enl : (502008/1000000:ℝ)^4≤Real.exp (-4*r) :=
    ennl.1.trans (Real.exp_le_exp.mpr (by linarith [hb.2]))
  have enh : Real.exp (-4*r)≤(502060/1000000:ℝ)^4 :=
    (Real.exp_le_exp.mpr (by linarith [hb.1])).trans ennh.2
  let ql : ℝ := 2*(1991794/1000000)-(502060/1000000)^4-1
  let qh : ℝ := 2*(1991987/1000000)-(502008/1000000)^4-1
  have hql : ql≤2*Real.exp r-Real.exp (-4*r)-1 := by dsimp [ql];linarith
  have hqh : 2*Real.exp r-Real.exp (-4*r)-1≤qh := by dsimp [qh];linarith
  have hqlpos : 0<ql := by norm_num [ql]
  have hqpos : 0<2*Real.exp r-Real.exp (-4*r)-1 := lt_of_lt_of_le hqlpos hql
  have hl : (14511/10000:ℝ)*ql<(1/r)*(2*Real.exp r-Real.exp (-4*r)-1) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right htl hqlpos)
      (mul_le_mul_of_nonneg_left hql (one_div_pos.mpr hrpos).le)
  have hh : (1/r)*(2*Real.exp r-Real.exp (-4*r)-1)<(14513/10000:ℝ)*qh := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqh (one_div_pos.mpr hrpos).le)
      (mul_lt_mul_of_pos_right hth (lt_of_lt_of_le hqpos hqh))
  have hp : shelfThreshold 5 1 (1/r)=(1/r)*(2*Real.exp r-Real.exp (-4*r)-1) := by
    rw [actual_shelf_threshold_equivalent_form]
    congr 1 <;> simp <;> ring
  refine ⟨htl,hth,?_,?_⟩ <;> rw [hp]
  · have hn : (847/200:ℝ)<(14511/10000:ℝ)*ql := by norm_num [ql]
    exact hn.trans hl
  · have hn : (14513/10000:ℝ)*qh<(849/200:ℝ) := by norm_num [qh]
    exact hh.trans hn

theorem actual_shelf_global_shape_at_its_profile_root
    (r : ℝ) (hr : r∈Ioo derivativeTurningPoint 1) (her : shelfDerivativeProfile r=0)
    (hpositive : ∀ x : ℝ, 0<x → x<r → 0<shelfDerivativeProfile x)
    (hnegative : ∀ x : ℝ, r<x → shelfDerivativeProfile x<0) :
    0<1/r ∧ StrictAntiOn (shelfThreshold 5 1) (Ioc 0 (1/r)) ∧
      StrictMonoOn (shelfThreshold 5 1) (Ici (1/r)) ∧
      (∀ tau : ℝ, 0<tau → tau≠1/r →
        shelfThreshold 5 1 (1/r)<shelfThreshold 5 1 tau) := by
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
  refine ⟨hstar,hanti,hmono,?_⟩
  intro tau ht hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact hanti ⟨ht,hlt.le⟩ ⟨hstar,le_rfl⟩ hlt
  · exact hmono (by simp only [Set.mem_Ici]; exact le_rfl) hgt.le hgt


theorem actual_shelf_exact_global_minimum_rounds_to_four_point_two_four_near_tau_one_point_four_five :
    ∃ tauStar : ℝ, (14511/10000:ℝ)<tauStar ∧ tauStar<(14513/10000:ℝ) ∧
      (847/200:ℝ)<shelfThreshold 5 1 tauStar ∧
      shelfThreshold 5 1 tauStar<(849/200:ℝ) ∧
      StrictAntiOn (shelfThreshold 5 1) (Ioc 0 tauStar) ∧
      StrictMonoOn (shelfThreshold 5 1) (Ici tauStar) ∧
      (∀ tau : ℝ,0<tau → tau≠tauStar →
        shelfThreshold 5 1 tauStar<shelfThreshold 5 1 tau) := by
  obtain ⟨r,hr,her,hp,hn⟩ := actual_shelf_positive_profile_root_exists_uniquely
  have hb := actual_shelf_minimum_location_and_value_rounding r hr her
  have hs := actual_shelf_global_shape_at_its_profile_root r hr her hp hn
  exact ⟨1/r,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hs.2.1,hs.2.2.1,hs.2.2.2⟩

end SafeLearning.CompleteModulesShelfGlobalShape30

namespace SafeLearning.CompleteModulesShelfGlobalShape30

theorem actual_shelf_threshold_small_tau_lower_bound (tau : ℝ) (ht : 0<tau) :
    2+1/tau ≤ shelfThreshold 5 1 tau := by
  have hq := Real.quadratic_le_exp_of_nonneg (one_div_pos.mpr ht).le
  have hm := mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤2*tau by positivity)
  have hn : Real.exp (-4/tau)≤1 := by
    have h := Real.exp_le_exp.mpr (show (-4:ℝ)/tau≤0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) ht.le)
    simpa using h
  have hmn := mul_le_mul_of_nonneg_left hn ht.le
  have hid : 2*tau*(1+1/tau+(1/tau)^2/2)=2*tau+2+1/tau := by
    field_simp <;> ring
  rw [hid] at hm
  rw [actual_shelf_threshold_equivalent_form]
  norm_num
  simp only [one_div] at hm hmn ⊢
  nlinarith

theorem actual_shelf_penalty_diverges_at_small_positive_tau :
    Tendsto (shelfThreshold 5 1) (𝓝[>] (0:ℝ)) atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))
  filter_upwards [self_mem_nhdsWithin] with tau ht
  change 0<tau at ht
  have h := actual_shelf_threshold_small_tau_lower_bound tau ht
  simpa only [one_div] using (show 1/tau ≤ shelfThreshold 5 1 tau by linarith)

theorem actual_shelf_failure_exponential_diverges_at_small_positive_tau :
    Tendsto (fun tau : ℝ => Real.exp (1/tau)) (𝓝[>] (0:ℝ)) atTop := by
  simpa only [one_div,Function.comp_def] using Real.tendsto_exp_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))

end SafeLearning.CompleteModulesShelfGlobalShape30
