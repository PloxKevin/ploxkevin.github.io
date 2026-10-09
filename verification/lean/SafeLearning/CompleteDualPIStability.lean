import SafeLearning.CompleteDualPIJury
import SafeLearning.CompleteDualPIRecurrenceDecay

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped Topology
open SafeLearning.CompleteDualPILinearModel
open SafeLearning.CompleteDualPIJury
open SafeLearning.CompleteDualPIRecurrenceDecay
namespace SafeLearning.CompleteDualPIStability

theorem actual_complex_loop_eigenmode (a c kp ki : ℝ) (z : ℂ)
    (hz : characteristic (1+a-c*(kp+ki)) (a-c*kp) z=0) (n : ℕ) :
    (z-1)*z^(n+1)=((a-c*(kp+ki):ℝ):ℂ)*((z-1)*z^n)-((c*ki:ℝ):ℂ)*z^n ∧
      z^(n+1)=z^n+(z-1)*z^n := by
  constructor
  · unfold characteristic at hz
    push_cast at hz ⊢
    rw [pow_succ]
    linear_combination z^n*hz
  · rw [pow_succ]
    ring

theorem every_actual_loop_trajectory_decays_iff_all_roots_stable (a c kp ki : ℝ) :
    (∀ state : ℕ→ℝ×ℝ,
      (∀ n,state (n+1)=loopStep a c kp ki (state n).1 (state n).2) →
      Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
        Tendsto (fun n=>(state n).2) atTop (𝓝 0)) ↔
      (∀ z : ℂ,characteristic (1+a-c*(kp+ki)) (a-c*kp) z=0 → ‖z‖<1) := by
  constructor
  · intro hall z hz
    let realState : ℕ→ℝ×ℝ := fun n=>(((z-1)*z^n).re,(z^n).re)
    let imagState : ℕ→ℝ×ℝ := fun n=>(((z-1)*z^n).im,(z^n).im)
    have hreloop (n : ℕ) : realState (n+1)=
        loopStep a c kp ki (realState n).1 (realState n).2 := by
      obtain ⟨h1,h2⟩ := actual_complex_loop_eigenmode a c kp ki z hz n
      apply Prod.ext
      · simpa only [realState,loopStep,Complex.sub_re,Complex.mul_re,
          Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using
          congrArg Complex.re h1
      · simpa only [realState,loopStep,Complex.add_re] using congrArg Complex.re h2
    have himloop (n : ℕ) : imagState (n+1)=
        loopStep a c kp ki (imagState n).1 (imagState n).2 := by
      obtain ⟨h1,h2⟩ := actual_complex_loop_eigenmode a c kp ki z hz n
      apply Prod.ext
      · simpa only [imagState,loopStep,Complex.sub_im,Complex.mul_im,
          Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero] using
          congrArg Complex.im h1
      · simpa only [imagState,loopStep,Complex.add_im] using congrArg Complex.im h2
    have hre : Tendsto (fun n=>(z^n).re) atTop (𝓝 0) := (hall realState hreloop).2
    have him : Tendsto (fun n=>(z^n).im) atTop (𝓝 0) := (hall imagState himloop).2
    have hp : Tendsto (fun n : ℕ=>z^n) atTop (𝓝 0) := by
      have h := ((Complex.continuous_ofReal.tendsto 0).comp hre).add
        (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
      simpa only [Function.comp_def,Complex.re_add_im,Complex.ofReal_zero,
        zero_mul,zero_add] using h
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hp
  · intro hstable state hloop
    exact actual_every_control_loop_coordinate_decays_when_roots_stable a c kp ki
      hstable state hloop

theorem actual_all_source_uncurved_trajectories_decay_iff_gain_region (c kp ki : ℝ) :
    (∀ state : ℕ→ℝ×ℝ,
      (∀ n,state (n+1)=loopStep 1 c kp ki (state n).1 (state n).2) →
      Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
        Tendsto (fun n=>(state n).2) atTop (𝓝 0)) ↔
      0<c*kp ∧ c*kp<2 ∧ 0<c*ki ∧ c*(2*kp+ki)<4 := by
  rw [every_actual_loop_trajectory_decays_iff_all_roots_stable]
  have h := actual_curved_spectral_stability_region 1 c kp ki
  norm_num at h
  convert h using 1 <;> norm_num

theorem actual_all_curved_trajectories_decay_iff_gain_region (a c kp ki : ℝ) :
    (∀ state : ℕ→ℝ×ℝ,
      (∀ n,state (n+1)=loopStep a c kp ki (state n).1 (state n).2) →
      Tendsto (fun n=>(state n).1) atTop (𝓝 0) ∧
        Tendsto (fun n=>(state n).2) atTop (𝓝 0)) ↔
      a-1<c*kp ∧ c*kp<a+1 ∧ 0<c*ki ∧ c*(2*kp+ki)<2*(1+a) := by
  rw [every_actual_loop_trajectory_decays_iff_all_roots_stable,
    actual_curved_spectral_stability_region]

end SafeLearning.CompleteDualPIStability
