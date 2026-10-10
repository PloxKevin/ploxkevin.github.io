import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SafeLearning.CompleteAppliedIntegratorEnergy

def window : Measure ℝ := volume.restrict (Ioc (0:ℝ) 2)
instance : IsFiniteMeasure window := by
  unfold window;infer_instance

theorem actual_window_mass : window.real univ=2 := by
  norm_num [window,measureReal_def]

theorem actual_window_integral_constant (c : ℝ) : (∫_t : ℝ,c ∂window)=2*c := by
  rw [integral_const,actual_window_mass];rfl

theorem actual_horizon_two_cauchy_schwarz_energy_bound (u : ℝ→ℝ)
    (hu : MemLp u 2 window) :
    (∫t,u t ∂window)^2≤2*(∫t,u t^2 ∂window) := by
  have hi := MemLp.integrable (by norm_num : (1:ℝ≥0∞)≤2) hu
  have hi2 := hu.integrable_sq
  let m : ℝ := (∫t,u t ∂window)/2
  have hnonnegative : 0≤∫t,(u t-m)^2 ∂window :=
    integral_nonneg (fun t=>sq_nonneg (u t-m))
  have he : (fun t : ℝ=>(u t-m)^2)=
      (fun t : ℝ=>u t^2-(2*m)*u t+m^2) := by
    funext t;ring
  rw [he] at hnonnegative
  rw [integral_add (f:=fun t : ℝ=>u t^2-(2*m)*u t) (g:=fun _t : ℝ=>m^2)
      (hi2.sub (hi.const_mul (2*m))) (integrable_const (m^2)),
    integral_sub (f:=fun t : ℝ=>u t^2) (g:=fun t : ℝ=>(2*m)*u t)
      hi2 (hi.const_mul (2*m)),integral_const_mul,
    actual_window_integral_constant] at hnonnegative
  dsimp [m] at hnonnegative
  nlinarith

theorem actual_existing_integrator_trajectory_has_the_endpoint_integral
    (x u : ℝ→ℝ) (hx : AbsolutelyContinuousOnInterval x 0 2)
    (hode : ∀ᵐt ∂volume,t∈Icc (0:ℝ) 2→HasDerivAt x (u t) t) :
    (∫t,u t ∂window)=x 2-x 0 := by
  have hi : (∫t in (0:ℝ)..2,u t)=(∫t in (0:ℝ)..2,deriv x t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hode] with t ht hmem
    have hcc : t∈Icc (0:ℝ) 2 := by
      have h : t∈Ioc (0:ℝ) 2 := by simpa using hmem
      exact ⟨h.1.le,h.2⟩
    exact (ht hcc).deriv.symm
  rw [hx.integral_deriv_eq_sub] at hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2)] at hi
  exact hi

def admissibleEnergies : Set ℝ :=
  {energy | ∃u : ℝ→ℝ,MemLp u 2 window ∧ (∫t,u t ∂window)=1 ∧
    (∫t,u t^2 ∂window)=energy}

theorem actual_constant_input_reaches_one_and_has_half_energy :
    MemLp (fun _t : ℝ=>(1/2:ℝ)) 2 window ∧
    (∫_t : ℝ,(1/2:ℝ) ∂window)=1 ∧
    (∫_t : ℝ,(1/2:ℝ)^2 ∂window)=1/2 ∧
    (∀t : ℝ,HasDerivAt (fun s : ℝ=>s/2) (1/2) t) ∧
    (0:ℝ)/2=0 ∧ (2:ℝ)/2=1 := by
  refine ⟨memLp_const _,?_,?_,?_,by norm_num,by norm_num⟩
  · rw [actual_window_integral_constant];norm_num
  · rw [actual_window_integral_constant];norm_num
  · intro t
    convert (hasDerivAt_id t).div_const 2 using 1 <;> simp

theorem actual_horizon_two_gramian_and_true_minimum_energy :
    (∫_t in (0:ℝ)..2,(1:ℝ))=2 ∧
    IsLeast admissibleEnergies (1/2:ℝ) ∧ (1:ℝ)^2/2=1/2 := by
  refine ⟨by norm_num,?_,by norm_num⟩
  constructor
  · have h := actual_constant_input_reaches_one_and_has_half_energy
    exact ⟨fun _=>(1/2:ℝ),h.1,h.2.1,h.2.2.1⟩
  · rintro energy ⟨u,hu,hendpoint,rfl⟩
    have h := actual_horizon_two_cauchy_schwarz_energy_bound u hu
    rw [hendpoint] at h
    nlinarith

theorem actual_every_finite_energy_integrator_control_reaching_one_obeys_the_optimal_bound
    (x u : ℝ→ℝ) (hx : AbsolutelyContinuousOnInterval x 0 2)
    (hu : MemLp u 2 window) (h0 : x 0=0) (h2 : x 2=1)
    (hode : ∀ᵐt ∂volume,t∈Icc (0:ℝ) 2→HasDerivAt x (u t) t) :
    (1/2:ℝ)≤∫t,u t^2 ∂window := by
  have he := actual_existing_integrator_trajectory_has_the_endpoint_integral x u hx hode
  rw [h0,h2,sub_zero] at he
  exact (actual_horizon_two_gramian_and_true_minimum_energy.2.1).2 ⟨u,hu,he,rfl⟩

end SafeLearning.CompleteAppliedIntegratorEnergy
