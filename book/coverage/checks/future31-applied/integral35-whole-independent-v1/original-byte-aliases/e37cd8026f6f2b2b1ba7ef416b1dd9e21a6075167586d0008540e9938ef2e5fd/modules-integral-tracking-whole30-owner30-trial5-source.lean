import SafeLearning.CompleteModulesTanhChords
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace SafeLearning.CompleteModulesIntegralTrackingWhole30
open CompleteModulesTheory CompleteModulesTanhChords

def nominalNetwork (r x : ℝ) : ℝ := r/2-(3/10)*Real.tanh (x-r)
def scalarMap (b d r x : ℝ) : ℝ := x/2+b*nominalNetwork r x+d

theorem actual_nominal_network_has_exact_equilibrium_feedforward (r : ℝ) :
    nominalNetwork r r=r/2 ∧ scalarMap 1 0 r r=r := by
  simp [nominalNetwork,scalarMap,Real.tanh_zero]

theorem actual_scalar_plant_equilibrium_has_the_printed_offset_equation
    (b d r e : ℝ) : scalarMap b d r (r+e)=r+e ↔
      e/2+(3*b/10)*Real.tanh e=(b-1)*r/2+d := by
  simp only [scalarMap,nominalNetwork,add_sub_cancel_left]
  constructor <;> intro h <;> linarith

theorem actual_both_scalar_loops_are_true_global_contractions
    (b d r : ℝ) (hb : b∈Icc 1 (6/5)) :
    ContractingWith (1/2 : ℝ≥0) (scalarMap b d r) := by
  have hb0 : 0≤b := by linarith [hb.1]
  have hd (x : ℝ) : HasDerivAt (scalarMap b d r)
      (1/2-(3*b/10)*(1-(Real.tanh (x-r))^2)) x := by
    have ht := ((actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x-r)).1).comp x
      ((hasDerivAt_id x).sub_const r)
    have hp := ((hasDerivAt_id x).div_const 2).add
      (((ht.const_mul (3/10)).const_sub (r/2)).const_mul b)
    convert hp.add_const d using 1
    · funext y; rfl
    · ring
  refine ⟨by norm_num,?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x; exact (hd x).differentiableAt
  · intro x
    rw [(hd x).deriv]
    have ht := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x-r)).2
    have hp : 0 ≤ (3*b/10)*(1-(Real.tanh (x-r))^2) := mul_nonneg (by positivity) ht.1.le
    have hu : (3*b/10)*(1-(Real.tanh (x-r))^2) ≤ 9/25 := by
      have h := mul_le_mul_of_nonneg_left ht.2 (show 0≤3*b/10 by positivity)
      nlinarith [hb.2]
    exact_mod_cast (show |1/2-(3*b/10)*(1-(Real.tanh (x-r))^2)| ≤ (1/2:ℝ) by
      rw [abs_of_nonneg (by linarith)];linarith)

theorem actual_scalar_loops_have_unique_equilibria_and_all_trajectories_converge
    (b d r : ℝ) (hb : b∈Icc 1 (6/5)) :
    ∃ xstar : ℝ, scalarMap b d r xstar=xstar ∧
      (∀ y,scalarMap b d r y=y → y=xstar) ∧
      ∀ x,Tendsto (fun n : ℕ => (scalarMap b d r)^[n] x) atTop (𝓝 xstar) := by
  let h := actual_both_scalar_loops_are_true_global_contractions b d r hb
  refine ⟨ContractingWith.fixedPoint (scalarMap b d r) h,h.fixedPoint_isFixedPt,?_,?_⟩
  · intro y hy; exact h.fixedPoint_unique hy
  · intro x;exact h.tendsto_iterate_fixedPoint x

theorem actual_positive_equilibrium_offset_budget_forces_nonzero_tracking_error
    (b d r e : ℝ) (he : scalarMap b d r (r+e)=r+e)
    (hq : 0<(b-1)*r/2+d) : e≠0 := by
  intro hz
  have h := (actual_scalar_plant_equilibrium_has_the_printed_offset_equation b d r e).mp he
  rw [hz,Real.tanh_zero] at h
  nlinarith

def integralEquilibrium (b d r : ℝ) : ℝ := ((1-b)*r/2-d)/(b/5)
def augmentedStep (b d r : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1/2+b*(z.2/5+nominalNetwork r z.1)+d,z.2+r-z.1)
def errorStep (b : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1/2-(3*b/10)*Real.tanh z.1+(b/5)*z.2,z.2-z.1)
def storage (z : ℝ×ℝ) : ℝ := 8*z.1^2-4*z.1*z.2+2*z.2^2

theorem actual_every_augmented_equilibrium_has_zero_output_offset
    (b d r : ℝ) (z : ℝ×ℝ) (hz : augmentedStep b d r z=z) : z.1=r := by
  have h := congrArg Prod.snd hz
  dsimp [augmentedStep] at h
  linarith

theorem actual_integral_equilibrium_exists_for_every_nonzero_gain
    (b d r : ℝ) (hb : b≠0) :
    augmentedStep b d r (r,integralEquilibrium b d r)=(r,integralEquilibrium b d r) := by
  apply Prod.ext
  · simp only [augmentedStep,nominalNetwork,sub_self,Real.tanh_zero,mul_zero,sub_zero,integralEquilibrium]
    field_simp
    ring
  · simp [augmentedStep]

theorem actual_augmented_physical_loop_has_the_true_centered_error_dynamics
    (b d r e eta : ℝ) (hb : b≠0) :
    augmentedStep b d r (r+e,integralEquilibrium b d r+eta)=
      (r+(errorStep b (e,eta)).1,integralEquilibrium b d r+(errorStep b (e,eta)).2) := by
  apply Prod.ext
  · simp only [augmentedStep,errorStep,nominalNetwork,add_sub_cancel_left,integralEquilibrium]
    field_simp
    ring
  · dsimp [augmentedStep,errorStep];ring

theorem actual_storage_has_uniform_positive_lower_and_upper_bounds (z : ℝ×ℝ) :
    z.1^2+z.2^2≤ storage z ∧ storage z≤10*(z.1^2+z.2^2) := by
  dsimp [storage]
  constructor
  · nlinarith [sq_nonneg (2*z.1-z.2),sq_nonneg z.1]
  · nlinarith [sq_nonneg (z.1+z.2),sq_nonneg z.2]

theorem actual_four_endpoint_drops_are_genuinely_positive (e eta : ℝ) :
    (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage (e/2+eta/5,eta-e) ∧
    (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage (e/5+eta/5,eta-e) ∧
    (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage (e/2+(6/25)*eta,eta-e) ∧
    (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage ((7/50)*e+(6/25)*eta,eta-e) := by
  dsimp [storage]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (e-eta),sq_nonneg e,sq_nonneg eta]
  · nlinarith [sq_nonneg (2*e-eta),sq_nonneg e,sq_nonneg eta]
  · nlinarith [sq_nonneg (2*e-eta),sq_nonneg e,sq_nonneg eta]
  · nlinarith [sq_nonneg (2*e-eta),sq_nonneg e,sq_nonneg eta]

theorem actual_every_slope_in_the_full_tanh_sector_has_uniform_storage_drop
    (b s e eta : ℝ) (hb : b=1 ∨ b=6/5) (hs : s∈Icc 0 1) :
    (1/4)*(e^2+eta^2)≤ storage (e,eta)-
      storage ((1/2-3*b*s/10)*e+(b/5)*eta,eta-e) := by
  have he : storage (e,eta)-storage ((1/2-3*b*s/10)*e+(b/5)*eta,eta-e)=
      (1-s)*(storage (e,eta)-storage (e/2+(b/5)*eta,eta-e))+
      s*(storage (e,eta)-storage ((1/2-3*b/10)*e+(b/5)*eta,eta-e))+
      8*(3*b/10)^2*e^2*s*(1-s) := by dsimp [storage];ring
  have hn : 0≤8*(3*b/10)^2*e^2*s*(1-s) := by
    have h1 : 0≤1-s := sub_nonneg.mpr hs.2
    have h0 : 0 ≤ s := hs.1
    positivity
  have endpoints := actual_four_endpoint_drops_are_genuinely_positive e eta
  have h0 : (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage (e/2+(b/5)*eta,eta-e) := by
    rcases hb with rfl|rfl
    · convert endpoints.1 using 1 <;> dsimp [storage] <;> ring
    · convert endpoints.2.2.1 using 1 <;> dsimp [storage] <;> ring
  have h1 : (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage ((1/2-3*b/10)*e+(b/5)*eta,eta-e) := by
    rcases hb with rfl|rfl
    · convert endpoints.2.1 using 1 <;> dsimp [storage] <;> ring
    · convert endpoints.2.2.2 using 1 <;> dsimp [storage] <;> ring
  rw [he]
  have w0 := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hs.2)
  have w1 := mul_le_mul_of_nonneg_left h1 hs.1
  nlinarith

theorem actual_augmented_tanh_loop_has_uniform_quadratic_contraction
    (b : ℝ) (hb : b=1 ∨ b=6/5) (z : ℝ×ℝ) :
    storage (errorStep b z)≤(39/40)*storage z := by
  obtain ⟨s,hs,ht⟩ : ∃ s : ℝ,s∈Icc 0 1 ∧ Real.tanh z.1=s*z.1 := by
    by_cases hz : z.1=0
    · exact ⟨0,by norm_num,by simp [hz]⟩
    · refine ⟨Real.tanh z.1/z.1,?_,?_⟩
      have h := actual_tanh_chord_quotient_is_positive_and_at_most_one z.1 0 hz
      simp only [Real.tanh_zero,sub_zero] at h
      exact ⟨h.1.le,h.2⟩
      exact (div_mul_cancel₀ _ hz).symm
  have h := actual_every_slope_in_the_full_tanh_sector_has_uniform_storage_drop b s z.1 z.2 hb hs
  have he : errorStep b z=((1/2-3*b*s/10)*z.1+(b/5)*z.2,z.2-z.1) := by
    apply Prod.ext
    · dsimp [errorStep];rw [ht];ring
    · rfl
  rw [he]
  have hu := (actual_storage_has_uniform_positive_lower_and_upper_bounds z).2
  nlinarith

def errorTrajectory (b : ℝ) (z : ℝ×ℝ) : ℕ→ℝ×ℝ
  | 0 => z
  | n+1 => errorStep b (errorTrajectory b z n)

theorem actual_all_time_augmented_storage_has_geometric_decay
    (b : ℝ) (hb : b=1 ∨ b=6/5) (z : ℝ×ℝ) (n : ℕ) :
    storage (errorTrajectory b z n)≤(39/40)^n*storage z := by
  induction n with
  | zero => simp [errorTrajectory]
  | succ n ih =>
    have h := actual_augmented_tanh_loop_has_uniform_quadratic_contraction b hb (errorTrajectory b z n)
    change storage (errorTrajectory b z (n+1))≤(39/40)*storage (errorTrajectory b z n) at h
    apply h.trans
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤39/40)
    simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hm

end SafeLearning.CompleteModulesIntegralTrackingWhole30

namespace SafeLearning.CompleteModulesIntegralTrackingWhole30

theorem actual_every_augmented_error_coordinate_tends_to_zero
    (b : ℝ) (hb : b=1 ∨ b=6/5) (z : ℝ×ℝ) :
    Tendsto (fun n => (errorTrajectory b z n).1) atTop (𝓝 0) ∧
    Tendsto (fun n => (errorTrajectory b z n).2) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (39/40:ℝ)^n*storage z) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤39/40) (by norm_num : (39/40:ℝ)<1)).mul_const (storage z)
  have hs (n : ℕ) : (errorTrajectory b z n).1^2+(errorTrajectory b z n).2^2 ≤
      (39/40:ℝ)^n*storage z :=
    (actual_storage_has_uniform_positive_lower_and_upper_bounds _).1.trans
      (actual_all_time_augmented_storage_has_geometric_decay b hb z n)
  have hsq1 : Tendsto (fun n => (errorTrajectory b z n).1^2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (fun n => by
      have h := hs n; nlinarith [sq_nonneg (errorTrajectory b z n).2]) hg
  have hsq2 : Tendsto (fun n => (errorTrajectory b z n).2^2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (fun n => by
      have h := hs n; nlinarith [sq_nonneg (errorTrajectory b z n).1]) hg
  constructor
  · apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq1
  · apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq2

def physicalTrajectory (b d r : ℝ) (z : ℝ×ℝ) : ℕ→ℝ×ℝ
  | 0 => z
  | n+1 => augmentedStep b d r (physicalTrajectory b d r z n)

theorem actual_every_physical_augmented_trajectory_is_the_centered_error_trajectory
    (b d r : ℝ) (hb : b≠0) (z : ℝ×ℝ) (n : ℕ) :
    physicalTrajectory b d r z n =
      (r+(errorTrajectory b (z.1-r,z.2-integralEquilibrium b d r) n).1,
       integralEquilibrium b d r+
         (errorTrajectory b (z.1-r,z.2-integralEquilibrium b d r) n).2) := by
  induction n with
  | zero => simp [physicalTrajectory,errorTrajectory]
  | succ n ih =>
    rw [physicalTrajectory,ih]
    simpa only [errorTrajectory] using
      actual_augmented_physical_loop_has_the_true_centered_error_dynamics b d r
        (errorTrajectory b (z.1-r,z.2-integralEquilibrium b d r) n).1
        (errorTrajectory b (z.1-r,z.2-integralEquilibrium b d r) n).2 hb

theorem actual_integral_controller_tracks_every_reference_from_every_initial_state
    (b d r : ℝ) (hb : b=1 ∨ b=6/5) (z : ℝ×ℝ) :
    Tendsto (fun n => (physicalTrajectory b d r z n).1) atTop (𝓝 r) ∧
    Tendsto (fun n => (physicalTrajectory b d r z n).2) atTop
      (𝓝 (integralEquilibrium b d r)) := by
  have hn : b≠0 := by rcases hb with rfl|rfl <;> norm_num
  have h := actual_every_augmented_error_coordinate_tends_to_zero b hb
    (z.1-r,z.2-integralEquilibrium b d r)
  constructor
  · convert (tendsto_const_nhds.add h.1 :
      Tendsto (fun n => r+(errorTrajectory b
        (z.1-r,z.2-integralEquilibrium b d r) n).1) atTop (𝓝 (r+0))) using 1
    · funext n; rw [actual_every_physical_augmented_trajectory_is_the_centered_error_trajectory b d r hn z n]
    · simp
  · convert (tendsto_const_nhds.add h.2 :
      Tendsto (fun n => integralEquilibrium b d r+(errorTrajectory b
        (z.1-r,z.2-integralEquilibrium b d r) n).2) atTop
          (𝓝 (integralEquilibrium b d r+0))) using 1
    · funext n; rw [actual_every_physical_augmented_trajectory_is_the_centered_error_trajectory b d r hn z n]
    · simp

end SafeLearning.CompleteModulesIntegralTrackingWhole30
