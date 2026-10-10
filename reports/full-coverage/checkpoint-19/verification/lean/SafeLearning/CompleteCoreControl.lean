import Mathlib
import SafeLearning.BookApplications
import SafeLearning.CompleteBookProjects

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteCoreControl

/-- Integrating factor argument on an actual differentiable trajectory. -/
theorem barrier_integrating_factor (eta etaDot : ℝ → ℝ) (beta horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : ContinuousOn eta (Icc 0 horizon))
    (hd : ∀ t ∈ Ioo 0 horizon, HasDerivAt eta (etaDot t) t)
    (hb : ∀ t ∈ Ioo 0 horizon, -beta*eta t ≤ etaDot t)
    (t : ℝ) (ht : t ∈ Icc 0 horizon) :
    eta 0*Real.exp (-beta*t) ≤ eta t := by
  have hder : ∀ s ∈ Ioo 0 horizon,
      HasDerivAt (fun r => Real.exp (beta*r)*eta r)
        (Real.exp (beta*s)*(etaDot s+beta*eta s)) s := by
    intro s hs
    convert (((hasDerivAt_id s).const_mul beta).exp.mul (hd s hs)) using 1 <;>
      (try ext r) <;> dsimp <;> ring
  have hm : MonotoneOn (fun r => Real.exp (beta*r)*eta r) (Icc 0 horizon) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 horizon)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc)
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) (by linarith [hb s hs])
  have hfac := hm (by exact ⟨le_rfl,hT⟩) ht ht.1
  simp only [mul_zero,Real.exp_zero,one_mul] at hfac
  have hmul := mul_le_mul_of_nonneg_left hfac (le_of_lt (Real.exp_pos (-beta*t)))
  have he : Real.exp (-beta*t)*Real.exp (beta*t)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [← mul_assoc,he,one_mul] at hmul
  simpa only [mul_comm] using hmul

theorem barrier_invariance (eta etaDot : ℝ → ℝ) (beta horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : ContinuousOn eta (Icc 0 horizon))
    (hd : ∀ t ∈ Ioo 0 horizon, HasDerivAt eta (etaDot t) t)
    (hb : ∀ t ∈ Ioo 0 horizon, -beta*eta t ≤ etaDot t)
    (h0 : 0 ≤ eta 0) : ∀ t ∈ Icc 0 horizon, 0 ≤ eta t := by
  intro t ht
  exact (mul_nonneg h0 (le_of_lt (Real.exp_pos _))).trans
    (barrier_integrating_factor eta etaDot beta horizon hT hc hd hb t ht)

theorem clearance_from_derivative (d velocity : ℝ → ℝ) (a b speed : ℝ)
    (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivAt d (velocity t) t)
    (hi : IntervalIntegrable velocity volume a b)
    (hv : ∀ t ∈ Icc a b, |velocity t| ≤ speed) :
    |d b-d a| ≤ speed*(b-a) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa [uIcc_of_le hab] using ht)) hi
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := velocity) (C := speed) (fun t ht => by
      simpa only [Real.norm_eq_abs] using hv t
        (by simpa [uIcc_of_le hab] using (uIoc_subset_uIcc ht)))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  exact hh

theorem delayed_measurement_error (present old measured speed delay error : ℝ)
    (hm : |old-measured| ≤ error) (hv : |present-old| ≤ speed*delay) :
    |present-measured| ≤ error+speed*delay := by
  calc |present-measured| = |(present-old)+(old-measured)| := by ring_nf
       _ ≤ |present-old|+|old-measured| := abs_add_le _ _
       _ ≤ error+speed*delay := by linarith

theorem held_clearance_from_ode (d disturbance : ℝ → ℝ) (u w horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : ContinuousOn d (Icc 0 horizon))
    (hd : ∀ t ∈ Ioo 0 horizon, HasDerivAt d (u+disturbance t) t)
    (hw : ∀ t ∈ Ioo 0 horizon, -w ≤ disturbance t) :
    ∀ t ∈ Icc 0 horizon, d 0+(u-w)*t ≤ d t := by
  have hm : MonotoneOn (fun t => d t-(u-w)*t) (Icc 0 horizon) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 horizon)
      (hc.sub ((continuous_const.mul continuous_id).continuousOn))
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hd t ht).sub ((hasDerivAt_id t).const_mul (u-w))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      linarith [hw t ht]
  intro t ht
  have hh := hm ⟨le_rfl,hT⟩ ht ht.1
  simp only [mul_zero,sub_zero] at hh
  linarith

theorem held_clearance_safety (d disturbance : ℝ → ℝ) (u w horizon lower : ℝ)
    (hT : 0 ≤ horizon) (hc : ContinuousOn d (Icc 0 horizon))
    (hd : ∀ t ∈ Ioo 0 horizon, HasDerivAt d (u+disturbance t) t)
    (hw : ∀ t ∈ Ioo 0 horizon, -w ≤ disturbance t)
    (h0 : lower ≤ d 0) (hlower : 0 ≤ lower)
    (hterminal : 0 ≤ lower+(u-w)*horizon) :
    ∀ t ∈ Icc 0 horizon, 0 ≤ d t := by
  intro t ht
  have ha := SafeLearning.BookApplications.held_barrier_affine lower (u-w) horizon t
    hlower ht hterminal
  have hb := held_clearance_from_ode d disturbance u w horizon hT hc hd hw t ht
  linarith

theorem noisier_barrier_command :
    (35/100 : ℝ)-8/100=27/100 ∧
    (1/10 : ℝ)-(27/100)/(1/2) = -44/100 ∧
    (-44/100 : ℝ)-(-8/10)=36/100 ∧
    (27/100 : ℝ)+(1/2)*(-44/100-1/10)=0 ∧
    (27/100 : ℝ)+(1/2)*(-1/2-1/10) = -3/100 := by norm_num

theorem failed_drive_feasible (lower : ℝ) :
    (∃ u ∈ Icc (-8/10 : ℝ) 0, 1/10-2*lower ≤ u) ↔ 1/20 ≤ lower := by
  constructor
  · rintro ⟨u,hu,hs⟩
    linarith [hu.2]
  · intro h
    exact ⟨0,by norm_num,by linarith⟩

theorem failed_drive_boundary_impossible (horizon : ℝ) (hT : 0 < horizon) :
    ¬ ∃ u ≤ (0 : ℝ), 0 ≤ (u-1/10)*horizon := by
  rintro ⟨u,hu,hs⟩
  have hn := mul_neg_of_neg_of_pos (by linarith : u-1/10 < 0) hT
  linarith

theorem failed_drive_eventual_escape (initial u : ℝ) (hu : u ≤ 0) :
    ∃ t : ℝ, 0 < t ∧ initial+(u-1/10)*t < 0 := by
  refine ⟨10*(|initial|+1),by positivity,?_⟩
  have hi := le_abs_self initial
  have hp : 0 ≤ -u*(|initial|+1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

theorem nonpositive_drive_upper_trajectory (d u : ℝ → ℝ)
    (hd : ∀ t ≥ 0, HasDerivAt d (u t-1/10) t)
    (hu : ∀ t ≥ 0, u t ≤ 0) (t : ℝ) (ht : 0 ≤ t) : d t ≤ d 0-t/10 := by
  have hc : ContinuousOn d (Ici (0 : ℝ)) := by
    intro s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun s => d s+(1/10)*s) (Ici (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (hc.add ((continuous_const.mul continuous_id).continuousOn))
    · intro s hs
      rw [interior_Ici] at hs
      exact ((hd s (le_of_lt hs)).add ((hasDerivAt_id s).const_mul (1/10))).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      linarith [hu s (le_of_lt hs)]
  have hh := hm (by simp) ht ht
  simp only [mul_zero,add_zero] at hh
  linarith

theorem nonpositive_time_varying_drive_eventual_escape (d u : ℝ → ℝ)
    (hd : ∀ t ≥ 0, HasDerivAt d (u t-1/10) t)
    (hu : ∀ t ≥ 0, u t ≤ 0) : ∃ t : ℝ, 0 < t ∧ d t < 0 := by
  refine ⟨10*(|d 0|+1),by positivity,?_⟩
  have hh := nonpositive_drive_upper_trajectory d u hd hu (10*(|d 0|+1)) (by positivity)
  have hb := le_abs_self (d 0)
  linarith

theorem delayed_barrier_command :
    (5/100 : ℝ)+(9/10)*(1/10)=14/100 ∧
    (35/100 : ℝ)-14/100=21/100 ∧
    (1/10 : ℝ)-(21/100)/(1/2) = -32/100 ∧
    (21/100 : ℝ)+(1/2)*(-1/2-1/10) = -9/100 := by norm_num

theorem noisy_projection_optimal (u : ℝ) (hu : u ∈ Icc (-44/100 : ℝ) (8/10)) :
    ((-44/100 : ℝ)-(-8/10))^2 ≤ (u-(-8/10))^2 := by
  have h := SafeLearning.CompleteBookProjects.projectInterval_optimal
    (-44/100) (8/10) (-8/10) u (by norm_num) hu
  norm_num [SafeLearning.CompleteBookProjects.projectInterval] at h ⊢
  exact h

theorem delayed_projection_optimal (u : ℝ) (hu : u ∈ Icc (-32/100 : ℝ) (8/10)) :
    ((-32/100 : ℝ)-(-8/10))^2 ≤ (u-(-8/10))^2 := by
  have h := SafeLearning.CompleteBookProjects.projectInterval_optimal
    (-32/100) (8/10) (-8/10) u (by norm_num) hu
  norm_num [SafeLearning.CompleteBookProjects.projectInterval] at h ⊢
  exact h

theorem failed_drive_critical_only_zero (u : ℝ) (hu : u ∈ Icc (-8/10 : ℝ) 0)
    (hs : 1/10-2*(1/20 : ℝ) ≤ u) : u=0 := by linarith [hu.2]

theorem cube_defines_halfline (x : ℝ) : 0 ≤ x^3 ↔ 0 ≤ x := by
  exact Odd.pow_nonneg_iff (by decide : Odd 3)

theorem cube_boundary_derivative : HasDerivAt (fun x : ℝ => x^3) 0 0 := by
  convert (hasDerivAt_id (0 : ℝ)).pow 3 using 1 <;> (try ext x) <;> norm_num

theorem outward_trajectory_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => -t) (-1) t := by
  convert (hasDerivAt_id t).neg using 1 <;> (try ext x) <;> rfl

theorem zero_gradient_does_not_imply_invariance (t : ℝ) (ht : 0 < t) :
    (0 : ℝ)^3=0 ∧ (3*(0 : ℝ)^2)*(-1)=0 ∧ ¬ 0 ≤ (-t)^3 := by
  constructor;norm_num
  constructor;norm_num
  have hp := pow_pos ht 3
  exact not_le.mpr (by nlinarith : (-t)^3 < 0)

theorem continuous_feedback_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
  simpa using (hasDerivAt_id t).neg.exp

theorem continuous_feedback_positive (t : ℝ) : 0 < Real.exp (-t) := Real.exp_pos _

theorem held_first_interval_iff (horizon : ℝ) (hT : 0 ≤ horizon) :
    (∀ t ∈ Icc (0 : ℝ) horizon, 0 ≤ 1-t) ↔ horizon ≤ 1 := by
  constructor
  · intro h
    linarith [h horizon ⟨hT,le_rfl⟩]
  · intro h t ht
    linarith [ht.2]

theorem held_first_interval_counterexample : (1 : ℝ)-3/2 = -1/2 := by norm_num

theorem high_order_derivatives (p v : ℝ → ℝ) (u : ℝ → ℝ) (t : ℝ)
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v (u t) t) :
    HasDerivAt (fun s => v s+p s) (u t+v t) t := hv.add hp

theorem high_order_initial_check :
    (-4/10 : ℝ)+1=6/10 ∧
    (∀ u : ℝ, 0 ≤ u+2*(-4/10)+1 ↔ -2/10 ≤ u) ∧
    (1/10 : ℝ) ≥ 0 ∧ (-1 : ℝ)+1/10 < 0 := by
  constructor;norm_num
  constructor
  · intro u;constructor <;> intro h <;> linarith
  · norm_num

theorem input_to_state_square (x d bound : ℝ) (hd : |d| ≤ bound) :
    x-bound^2/4 ≤ x+x^4-x^2*d := by
  have hb := abs_le.mp hd
  have hs : d^2 ≤ bound^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg d) hd
    simpa only [← sq,sq_abs] using hh
  nlinarith [sq_nonneg (x^2-d/2)]

theorem input_to_state_inflated_boundary (x d bound : ℝ)
    (hd : |d| ≤ bound) (hx : x=2+bound^2/4) :
    0 ≤ x+x^4-x^2*d := by
  linarith [input_to_state_square x d bound hd]

theorem small_disturbance_boundary (r d : ℝ) (hr : r ∈ Icc 0 (1/4))
    (hd : |d| ≤ r) : -(2+r)+(2+r)^2*d < 0 := by
  have hdb := (abs_le.mp hd).2
  have hh := mul_le_mul_of_nonneg_left hdb (sq_nonneg (2+r))
  have hp : (2+r)*r ≤ (9/4)*(1/4) :=
    mul_le_mul (by linarith [hr.2]) hr.2 hr.1 (by norm_num)
  have hneg := mul_neg_of_pos_of_neg (by linarith [hr.1] : 0 < 2+r)
    (by linarith : -1+(2+r)*r < 0)
  nlinarith

end SafeLearning.CompleteCoreControl
