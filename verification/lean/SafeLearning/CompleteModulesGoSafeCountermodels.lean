import SafeLearning.CompleteModulesGoSafeBackupConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace SafeLearning.CompleteModulesGoSafeCountermodels
open CompleteModulesGoSafeBackupConsequences

theorem actual_positive_source_infimum_already_implies_bounded_below
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X)
    (hpositive : (1/5:ℝ) ≤ actualTrajectoryInfimum F margin x) :
    BddBelow (trajectoryMargins F margin x) := by
  by_contra h
  have hz : actualTrajectoryInfimum F margin x=0 := by
    unfold actualTrajectoryInfimum
    simpa using csInf_of_not_bddBelow h
  rw [hz] at hpositive
  norm_num at hpositive

theorem actual_literal_source_suffix_statement_needs_no_extra_boundedness_premise
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ)
    (ht : 0 ≤ time) (hpositive : (1/5:ℝ) ≤ actualTrajectoryInfimum F margin x) :
    (1/5:ℝ) ≤ actualTrajectoryInfimum F margin (F.path time x) :=
  actual_source_point_two_margin_is_retained_at_every_visited_state F margin x time ht
    (actual_positive_source_infimum_already_implies_bounded_below F margin x hpositive) hpositive

theorem actual_positive_source_trajectory_infimum_certifies_every_individual_time
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ)
    (ht : 0 ≤ time) (hpositive : (1/5:ℝ) ≤ actualTrajectoryInfimum F margin x) :
    (1/5:ℝ) ≤ margin (F.path time x) := by
  apply hpositive.trans
  apply csInf_le (actual_positive_source_infimum_already_implies_bounded_below F margin x hpositive)
  exact ⟨time,ht,rfl⟩

def sampleOnlyFastPath (t : ℝ) : ℝ := 1000*t^2

theorem actual_zero_speed_at_a_sample_does_not_certify_between_sample_motion :
    deriv sampleOnlyFastPath 0=0 ∧
      ‖deriv sampleOnlyFastPath 0‖ ≤ (3:ℝ) ∧
      (0:ℝ) ≤ 1/50 ∧ (1/50:ℝ) ≤ 1/50 ∧
      (3/50:ℝ) < ‖sampleOnlyFastPath (1/50)-sampleOnlyFastPath 0‖ := by
  have hd : HasDerivAt sampleOnlyFastPath (1000*(2*(0:ℝ))) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).pow 2).const_mul (1000:ℝ) using 1 <;> first | rfl | norm_num [sampleOnlyFastPath]
  have hzero : deriv sampleOnlyFastPath 0=0 := by simpa using hd.deriv
  rw [hzero]
  norm_num [sampleOnlyFastPath]

theorem actual_general_speed_bound_certifies_the_full_monitoring_and_delay_interval
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (path : ℝ→X) (sample interval time speed : ℝ)
    (hspeed_nonneg : 0 ≤ speed) (ht : sample ≤ time) (hend : time ≤ sample+interval)
    (hdiff : ∀ r∈Icc sample (sample+interval),DifferentiableAt ℝ path r)
    (hspeed : ∀ r∈Icc sample (sample+interval),‖deriv path r‖ ≤ speed) :
    ‖path time-path sample‖ ≤ (∫ r in sample..time,‖deriv path r‖) ∧
      (∫ r in sample..time,‖deriv path r‖) ≤ speed*(time-sample) ∧
      speed*(time-sample) ≤ speed*interval := by
  have hsub : Icc sample time⊆Icc sample (sample+interval) :=
    fun r hr=>⟨hr.1,hr.2.trans hend⟩
  have hcont : ContinuousOn path (Icc sample time) :=
    fun r hr=>(hdiff r (hsub hr)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ path (Ioo sample time) :=
    fun r hr=>(hdiff r (hsub ⟨hr.1.le,hr.2.le⟩)).differentiableWithinAt
  have hint : IntervalIntegrable (fun r=>‖deriv path r‖) volume sample time := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>speed) volume sample time).mono_fun
      (aestronglyMeasurable_deriv path _).norm
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [uIoc_of_le ht] at hr
    have hb := hspeed r (hsub ⟨hr.1.le,hr.2⟩)
    simpa only [norm_norm,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),abs_of_nonneg hspeed_nonneg] using hb
  constructor
  · apply norm_sub_le_integral_of_norm_deriv_le_of_le ht hcont hd _ hint
    exact Eventually.of_forall fun r hr=>le_refl _
  constructor
  · calc
      (∫ r in sample..time,‖deriv path r‖) ≤ (∫ _r in sample..time,speed) := by
        exact intervalIntegral.integral_mono_on ht hint intervalIntegrable_const
          (fun r hr=>hspeed r (hsub hr))
      _=speed*(time-sample) := by simp;ring
  · apply mul_le_mul_of_nonneg_left _ hspeed_nonneg
    linarith

end SafeLearning.CompleteModulesGoSafeCountermodels
