import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeCubicBarrier

def exponent : ℝ := 2/3
def alpha (r : ℝ) : ℝ := if r ≤ 0 then -3*(-r)^exponent else 3*r^exponent
def barrier (x : ℝ) : ℝ := -x^3
def safe : Set ℝ := {x | 0 ≤ barrier x}
def path (t : ℝ) : ℝ := -1+t

theorem actual_source_alpha_is_the_printed_signed_power (r : ℝ) :
    alpha r=3*Real.sign r*|r|^exponent := by
  rcases lt_trichotomy r 0 with hn|hz|hp
  · simp [alpha,hn.le,Real.sign_of_neg hn,abs_of_neg hn]
    ring
  · subst r
    norm_num [alpha,exponent]
  · simp [alpha,not_le.mpr hp,Real.sign_of_pos hp,abs_of_pos hp]

theorem actual_source_alpha_is_a_continuous_strictly_increasing_extended_class_K :
    Continuous alpha ∧ StrictMono alpha ∧ alpha 0=0 := by
  have hp : (0:ℝ)<exponent := by norm_num [exponent]
  have hc : Continuous (fun r : ℝ => r^exponent) := Real.continuous_rpow_const hp.le
  have hn : Continuous (fun r : ℝ => -3*(-r)^exponent) :=
    continuous_const.mul (hc.comp continuous_id.neg)
  have hpos : Continuous (fun r : ℝ => 3*r^exponent) := continuous_const.mul hc
  refine ⟨?_,?_,by norm_num [alpha,exponent]⟩
  · exact hn.if_le hpos continuous_id continuous_const (by intro r hr; simp only at hr; subst r; norm_num [exponent])
  · intro x y hxy
    by_cases hx : x≤0
    · by_cases hy : y≤0
      · have hr := Real.rpow_lt_rpow (by linarith : (0:ℝ)≤-y) (by linarith : -y < -x) hp
        simp only [alpha,if_pos hx,if_pos hy]
        linarith
      · have hypos : 0<y := lt_of_not_ge hy
        have hpow : 0<y^exponent := Real.rpow_pos_of_pos hypos exponent
        have hxpow : 0≤(-x)^exponent := Real.rpow_nonneg (by linarith) exponent
        simp only [alpha,if_pos hx,if_neg hy]
        nlinarith
    · have hxpos : 0<x := lt_of_not_ge hx
      have hy : ¬y≤0 := by linarith
      have hr := Real.rpow_lt_rpow hxpos.le hxy hp
      simp only [alpha,if_neg hx,if_neg hy]
      linarith

theorem actual_source_barrier_defines_the_negative_halfline_and_has_zero_boundary_gradient :
    safe=Iic (0:ℝ) ∧ ContDiff ℝ 1 barrier ∧
      (∀x : ℝ, HasDerivAt barrier (-3*x^2) x) ∧ HasDerivAt barrier 0 0 := by
  have hd : ∀x : ℝ, HasDerivAt barrier (-3*x^2) x := by
    intro x
    convert ((hasDerivAt_id x).pow 3).neg using 1 <;> simp [barrier] <;> ring
  refine ⟨?_,by unfold barrier; fun_prop,hd,?_⟩
  · ext x
    change 0 ≤ -x^3 ↔ x≤0
    rw [neg_nonneg,Odd.pow_nonpos_iff (by decide : Odd 3)]
  · simpa using hd 0

private theorem cube_rpow_two_thirds (x : ℝ) (hx : 0≤x) :
    (x^3)^exponent=x^2 := by
  calc
    (x^3)^exponent=x^((3:ℝ)*exponent) := (Real.rpow_natCast_mul hx 3 exponent).symm
    _=x^(2:ℝ) := by norm_num [exponent]
    _=x^2 := Real.rpow_natCast x 2

theorem actual_source_barrier_inequality_holds_with_equality_on_its_closed_safe_domain
    (x : ℝ) (hx : x≤0) : -3*x^2+alpha (barrier x)=0 := by
  have hp : 0≤barrier x := by
    change 0≤-x^3
    have h := (Odd.pow_nonpos_iff (by decide : Odd 3)).mpr hx
    linarith
  by_cases he : x=0
  · subst x; norm_num [alpha,barrier,exponent]
  · have hb : 0<barrier x := by
      have hxneg : x<0 := lt_of_le_of_ne hx he
      have hc : x^3<0 := (Odd.pow_neg_iff (by decide : Odd 3)).mpr hxneg
      dsimp [barrier]; linarith
    rw [alpha,if_neg (not_le.mpr hb)]
    have hc : barrier x=(-x)^3 := by unfold barrier; ring
    rw [hc,cube_rpow_two_thirds (-x) (by linarith)]
    ring

theorem actual_source_countertrajectory_solves_the_ODE_and_leaves_after_time_one :
    path 0=-1 ∧ (∀t : ℝ, HasDerivAt path 1 t) ∧
      path 0 ∈ safe ∧ ∀t : ℝ, 1<t → path t ∉ safe := by
  refine ⟨by norm_num [path],?_,?_,?_⟩
  · intro t; simpa [path] using (hasDerivAt_id t).const_add (-1)
  · rw [actual_source_barrier_defines_the_negative_halfline_and_has_zero_boundary_gradient.1]
    norm_num [path]
  · intro t ht
    rw [actual_source_barrier_defines_the_negative_halfline_and_has_zero_boundary_gradient.1]
    change ¬path t≤0
    unfold path
    linarith

theorem actual_source_inequality_fails_at_every_strictly_outside_state
    (x : ℝ) (hx : 0<x) : -3*x^2+alpha (barrier x)=-6*x^2 ∧ -3*x^2+alpha (barrier x)<0 := by
  have hb : barrier x≤0 := by unfold barrier; have h := pow_pos hx 3; linarith
  rw [alpha,if_pos hb]
  have hc : -barrier x=x^3 := by unfold barrier; ring
  rw [hc,cube_rpow_two_thirds x hx.le]
  constructor
  · ring
  · have hs := sq_pos_of_pos hx; nlinarith

end SafeLearning.CompleteModulesLandscapeCubicBarrier
