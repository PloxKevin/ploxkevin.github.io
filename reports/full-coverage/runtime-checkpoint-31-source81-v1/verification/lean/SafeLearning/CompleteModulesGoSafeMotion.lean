import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace SafeLearning.CompleteModulesGoSafeMotion

theorem actual_every_sample_interval_displacement_has_the_literal_speed_integral_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (path : ℝ→X) (sample interval time : ℝ)
    (ht : sample ≤ time) (hend : time ≤ sample+interval)
    (hdiff : ∀ r∈Icc sample (sample+interval),DifferentiableAt ℝ path r)
    (hspeed : ∀ r∈Icc sample (sample+interval),‖deriv path r‖ ≤ 3) :
    ‖path time-path sample‖ ≤ (∫ r in sample..time,‖deriv path r‖) ∧
      (∫ r in sample..time,‖deriv path r‖) ≤ 3*(time-sample) ∧
      3*(time-sample) ≤ 3*interval := by
  have hsub : Icc sample time⊆Icc sample (sample+interval) :=
    fun r hr=>⟨hr.1,hr.2.trans hend⟩
  have hcont : ContinuousOn path (Icc sample time) :=
    fun r hr=>(hdiff r (hsub hr)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ path (Ioo sample time) :=
    fun r hr=>(hdiff r (hsub ⟨hr.1.le,hr.2.le⟩)).differentiableWithinAt
  have hint : IntervalIntegrable (fun r=>‖deriv path r‖) volume sample time := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>(3:ℝ)) volume sample time).mono_fun
      (aestronglyMeasurable_deriv path _).norm
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [uIoc_of_le ht] at hr
    have hb := hspeed r (hsub ⟨hr.1.le,hr.2⟩)
    simpa only [norm_norm,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] using hb
  constructor
  · apply norm_sub_le_integral_of_norm_deriv_le_of_le ht hcont hd _ hint
    exact Eventually.of_forall fun r hr=>le_refl _
  constructor
  · calc
      (∫ r in sample..time,‖deriv path r‖) ≤ (∫ _r in sample..time,(3:ℝ)) := by
        exact intervalIntegral.integral_mono_on ht hint intervalIntegrable_const
          (fun r hr=>hspeed r (hsub hr))
      _=3*(time-sample) := by simp;ring
  · linarith

theorem actual_source_point_zero_two_and_doubled_motion_allowances :
    (3:ℝ)*(1/50)=3/50 ∧ (3:ℝ)*(1/25)=3/25 ∧
      (3:ℝ)*(1/25)=2*((3:ℝ)*(1/50)) := by norm_num

theorem actual_increasing_motion_allowance_can_only_shrink_a_fixed_backup_region
    {X : Type*} [PseudoMetricSpace X] (center : X) (lower L small large : ℝ)
    (hL : 0 ≤ L) (hallowance : small ≤ large) :
    {x | L*(dist x center+large) ≤ lower}⊆{x | L*(dist x center+small) ≤ lower} := by
  intro x hx
  exact (mul_le_mul_of_nonneg_left (by linarith) hL).trans hx

end SafeLearning.CompleteModulesGoSafeMotion
