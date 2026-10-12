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
    · simpa using endpoints.1
    · convert endpoints.2.2.1 using 1 <;> ring
  have h1 : (1/4)*(e^2+eta^2)≤ storage (e,eta)-storage ((1/2-3*b/10)*e+(b/5)*eta,eta-e) := by
    rcases hb with rfl|rfl
    · convert endpoints.2.1 using 1 <;> ring
    · convert endpoints.2.2.2 using 1 <;> ring
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
  · apply tendsto_zero_iff_abs_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq1
  · apply tendsto_zero_iff_abs_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero] using
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

namespace SafeLearning.CompleteModulesIntegralTrackingWhole30

def generalAugmentedStep (a b d r kXi : ℝ) (network : ℝ → ℝ → ℝ)
    (z : ℝ×ℝ) : ℝ×ℝ :=
  (a*z.1+b*(kXi*z.2+network z.1 r)+d,z.2+r-z.1)

theorem actual_integrator_zero_offset_is_independent_of_every_plant_and_network_parameter
    (a b d r kXi : ℝ) (network : ℝ → ℝ → ℝ) (z : ℝ×ℝ)
    (hz : generalAugmentedStep a b d r kXi network z=z) : z.1=r := by
  have h := congrArg Prod.snd hz
  dsimp [generalAugmentedStep] at h
  linarith

theorem actual_general_augmented_equilibrium_exists_without_network_weight_constraints
    (a b d r kXi : ℝ) (network : ℝ → ℝ → ℝ) (hb : b≠0) (hk : kXi≠0) :
    generalAugmentedStep a b d r kXi network
      (r,((1-a)*r-b*network r r-d)/(b*kXi))=
      (r,((1-a)*r-b*network r r-d)/(b*kXi)) := by
  apply Prod.ext
  · dsimp [generalAugmentedStep]
    field_simp
    ring
  · dsimp [generalAugmentedStep]
    ring

theorem actual_convergence_of_a_true_integral_loop_forces_exact_output_tracking
    (r xstar xistar : ℝ) (x xi : ℕ → ℝ)
    (hstep : ∀ n,xi (n+1)=xi n+r-x n)
    (hx : Tendsto x atTop (𝓝 xstar)) (hxi : Tendsto xi atTop (𝓝 xistar)) :
    xstar=r := by
  have hshift := hxi.comp (tendsto_add_atTop_nat 1)
  have hupdate := (hxi.add_const r).sub hx
  have he : (fun n => xi (n+1))=(fun n => xi n+r-x n) := by
    funext n;exact hstep n
  rw [←he] at hupdate
  have h := tendsto_nhds_unique hshift hupdate
  linarith

def offsetBalance (q e : ℝ) : ℝ := e/2+q*Real.tanh e

theorem actual_offset_balance_is_strictly_increasing_for_every_nonnegative_coefficient
    (q : ℝ) (hq : 0≤q) : StrictMono (offsetBalance q) := by
  intro x y hxy
  have hd : 0<y-x := sub_pos.mpr hxy
  have ht := (actual_tanh_chord_quotient_is_positive_and_at_most_one y x (ne_of_gt hxy)).1
  have hm := mul_pos ht hd
  rw [div_mul_cancel₀ _ hd.ne'] at hm
  have hqmul := mul_nonneg hq hm.le
  dsimp [offsetBalance]
  nlinarith

private theorem exact_tanh_double_exponential_ratio (x : ℝ) :
    Real.tanh x=(Real.exp (2*x)-1)/(Real.exp (2*x)+1) := by
  have he : Real.exp (2*x)=(Real.exp x)^2 := by
    rw [show 2*x=x+x by ring,Real.exp_add]
    ring
  rw [he,Real.tanh_eq,Real.exp_neg]
  have hn := Real.exp_ne_zero x
  have hp : (Real.exp x)^2+1≠0 := by positivity
  field_simp <;> ring

theorem actual_four_offset_bracket_exponentials_have_rigorous_rational_enclosures :
    (1.284410681:ℝ)<Real.exp 0.2503 ∧ Real.exp 0.2503<1.284410683 ∧
    (1.284667589:ℝ)<Real.exp 0.2505 ∧ Real.exp 0.2505<1.284667591 ∧
    (1.262255247:ℝ)<Real.exp 0.2329 ∧ Real.exp 0.2329<1.262255249 ∧
    (1.262507723:ℝ)<Real.exp 0.2331 ∧ Real.exp 0.2331<1.262507725 := by
  have h1 := abs_le.mp (Real.exp_bound (x:=(0.2503:ℝ)) (by norm_num) (n:=8) (by norm_num))
  have h2 := abs_le.mp (Real.exp_bound (x:=(0.2505:ℝ)) (by norm_num) (n:=8) (by norm_num))
  have h3 := abs_le.mp (Real.exp_bound (x:=(0.2329:ℝ)) (by norm_num) (n:=8) (by norm_num))
  have h4 := abs_le.mp (Real.exp_bound (x:=(0.2331:ℝ)) (by norm_num) (n:=8) (by norm_num))
  norm_num [Finset.sum_range_succ,Nat.factorial] at h1 h2 h3 h4
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem actual_both_offset_balance_equations_have_true_printed_rounding_brackets :
    offsetBalance (3/10) 0.12515<(0.1:ℝ) ∧ 0.1<offsetBalance (3/10) 0.12525 ∧
    offsetBalance (9/25) 0.11645<(0.1:ℝ) ∧ 0.1<offsetBalance (9/25) 0.11655 := by
  have h := actual_four_offset_bracket_exponentials_have_rigorous_rational_enclosures
  have h1 : Real.tanh 0.12515 < ((0.1:ℝ)-0.12515/2)/(3/10) := by
    rw [exact_tanh_double_exponential_ratio]
    norm_num only
    apply (div_lt_iff₀ (by positivity : 0<Real.exp 0.2503+1)).mpr
    nlinarith [h.2.1]
  have h2 : ((0.1:ℝ)-0.12525/2)/(3/10)<Real.tanh 0.12525 := by
    rw [exact_tanh_double_exponential_ratio]
    norm_num only
    apply (lt_div_iff₀ (by positivity : 0<Real.exp 0.2505+1)).mpr
    nlinarith [h.2.2.1]
  have h3 : Real.tanh 0.11645 < ((0.1:ℝ)-0.11645/2)/(9/25) := by
    rw [exact_tanh_double_exponential_ratio]
    norm_num only
    apply (div_lt_iff₀ (by positivity : 0<Real.exp 0.2329+1)).mpr
    nlinarith [h.2.2.2.2.1]
  have h4 : ((0.1:ℝ)-0.11655/2)/(9/25)<Real.tanh 0.11655 := by
    rw [exact_tanh_double_exponential_ratio]
    norm_num only
    apply (lt_div_iff₀ (by positivity : 0<Real.exp 0.2331+1)).mpr
    nlinarith [h.2.2.2.2.2.2.1]
  dsimp [offsetBalance]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem actual_equilibrium_offsets_are_nonzero_and_round_to_the_printed_four_decimals
    (eNom eGain : ℝ)
    (hNom : scalarMap 1 (1/10) 1 (1+eNom)=1+eNom)
    (hGain : scalarMap (6/5) 0 1 (1+eGain)=1+eGain) :
    0<eNom ∧ 0<eGain ∧ |eNom-0.1252|<0.00005 ∧ |eGain-0.1165|<0.00005 := by
  have hN := (actual_scalar_plant_equilibrium_has_the_printed_offset_equation 1 (1/10) 1 eNom).mp hNom
  have hG := (actual_scalar_plant_equilibrium_has_the_printed_offset_equation (6/5) 0 1 eGain).mp hGain
  have hn : offsetBalance (3/10) eNom=(0.1:ℝ) := by dsimp [offsetBalance];nlinarith [hN]
  have hg : offsetBalance (9/25) eGain=(0.1:ℝ) := by dsimp [offsetBalance];nlinarith [hG]
  have hmN := actual_offset_balance_is_strictly_increasing_for_every_nonnegative_coefficient (3/10) (by norm_num)
  have hmG := actual_offset_balance_is_strictly_increasing_for_every_nonnegative_coefficient (9/25) (by norm_num)
  have hs := actual_both_offset_balance_equations_have_true_printed_rounding_brackets
  have hnl : (0.12515:ℝ)<eNom := hmN.lt_iff_lt.mp (by rw [hn];exact hs.1)
  have hnu : eNom<(0.12525:ℝ) := hmN.lt_iff_lt.mp (by rw [hn];exact hs.2.1)
  have hgl : (0.11645:ℝ)<eGain := hmG.lt_iff_lt.mp (by rw [hg];exact hs.2.2.1)
  have hgu : eGain<(0.11655:ℝ) := hmG.lt_iff_lt.mp (by rw [hg];exact hs.2.2.2)
  refine ⟨by linarith,by linarith,abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

theorem actual_linearised_scalar_offset_and_integrator_state_exact_values_and_rounding :
    (1/10:ℝ)/(1-1/2+3/10)=1/8 ∧
    integralEquilibrium (6/5) (1/10) 1=(-5/6:ℝ) ∧
    |integralEquilibrium (6/5) (1/10) 1-(-0.833)|<0.0005 := by
  norm_num [integralEquilibrium]

end SafeLearning.CompleteModulesIntegralTrackingWhole30
