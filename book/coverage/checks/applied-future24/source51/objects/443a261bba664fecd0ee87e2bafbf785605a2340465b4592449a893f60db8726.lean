import SafeLearning.CompleteModulesGoSafeSamplingSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeSamplingConsequences
open CompleteModulesGoSafeBackupConsequences CompleteModulesGoSafeSamplingSafety

/-- A lower bound measured at the initial state remains a lower bound at every
stored state along the same complete-state backup flow. -/
theorem actual_initial_backup_lower_bound_applies_to_every_stored_suffix_state
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (initial : X)
    (lower time : ℝ) (ht : 0 ≤ time)
    (hbounded : BddBelow (trajectoryMargins F margin initial))
    (hlower : lower ≤ actualTrajectoryInfimum F margin initial) :
    lower ≤ actualTrajectoryInfimum F margin (F.path time initial) :=
  hlower.trans
    (actual_infimum_of_the_restarted_trajectory_cannot_be_smaller
      F margin initial time ht hbounded)

theorem actual_initial_measurement_and_stored_suffix_certificate_cover_the_trigger
    {X : Type*} [PseudoMetricSpace X] (F : ClosedLoop X) (margin : X→ℝ)
    (L : ℝ≥0) (hg : LipschitzWith L (actualTrajectoryInfimum F margin))
    (initial previous trigger : X) (lower time motion : ℝ) (ht : 0 ≤ time)
    (hbounded : BddBelow (trajectoryMargins F margin initial))
    (hlower : lower ≤ actualTrajectoryInfimum F margin initial)
    (hmove : dist trigger previous ≤ motion)
    (hprevious : (L:ℝ)*(dist previous (F.path time initial)+motion) ≤ lower) :
    lower ≤ actualTrajectoryInfimum F margin (F.path time initial) ∧
      0 ≤ actualTrajectoryInfimum F margin trigger := by
  have hstored := actual_initial_backup_lower_bound_applies_to_every_stored_suffix_state
    F margin initial lower time ht hbounded hlower
  refine ⟨hstored,?_⟩
  exact (actual_previous_sample_backup_remains_nonnegative_at_the_trigger_sample
    (actualTrajectoryInfimum F margin) L hg (F.path time initial) previous trigger
    lower motion hstored hmove hprevious).2.2

def actualContinuousExplorationPath (time : ℝ) : ℝ := time/20

theorem actual_between_sample_exploration_path_is_continuous :
    Continuous actualContinuousExplorationPath := by
  unfold actualContinuousExplorationPath
  continuity

theorem actual_between_sample_exploration_motion_bound_holds_throughout_the_interval :
    actualContinuousExplorationPath 0=0 ∧
      actualContinuousExplorationPath 1=1/20 ∧
      ∀ time∈Icc (0:ℝ) 1,
        dist (actualContinuousExplorationPath time) (actualContinuousExplorationPath 0)=time/20 ∧
        dist (actualContinuousExplorationPath time) (actualContinuousExplorationPath 0) ≤ 1/20 := by
  refine ⟨by norm_num [actualContinuousExplorationPath],
    by norm_num [actualContinuousExplorationPath],?_⟩
  intro time ht
  have hn : 0 ≤ time/20 := by linarith [ht.1]
  simp only [actualContinuousExplorationPath,zero_div,Real.dist_eq,sub_zero,abs_of_nonneg hn]
  exact ⟨True.intro,by linarith [ht.2]⟩

/-- The old test passes at the sampled safe boundary, yet this genuine
continuous exploration is unsafe at every strictly positive intersample time. -/
theorem actual_omitted_motion_tolerance_allows_unsafe_states_between_samples :
    (0:ℝ) ≥ 2*dist (actualContinuousExplorationPath 0) 0 ∧
      actualTrajectoryInfimum actualConstantBackup sourceUnsafeMargin
        (actualContinuousExplorationPath 0)=0 ∧
      (∀ time∈Ioc (0:ℝ) 1,
        sourceUnsafeMargin (actualContinuousExplorationPath time)= -time/10 ∧
        sourceUnsafeMargin (actualContinuousExplorationPath time)<0 ∧
        actualTrajectoryInfimum actualConstantBackup sourceUnsafeMargin
          (actualContinuousExplorationPath time)<0) ∧
      ¬((0:ℝ) ≥ 2*(dist (actualContinuousExplorationPath 0) 0+1/20)) := by
  refine ⟨by norm_num [actualContinuousExplorationPath],?_,?_,
    by norm_num [actualContinuousExplorationPath]⟩
  · rw [actual_constant_backup_trajectory_minimum_is_the_literal_state_margin]
    norm_num [actualContinuousExplorationPath,sourceUnsafeMargin]
  · intro time ht
    have hvalue : sourceUnsafeMargin (actualContinuousExplorationPath time)= -time/10 := by
      unfold sourceUnsafeMargin actualContinuousExplorationPath
      ring
    have hnegative : -time/10<0 := by linarith [ht.1]
    refine ⟨hvalue,hvalue ▸ hnegative,?_⟩
    rw [actual_constant_backup_trajectory_minimum_is_the_literal_state_margin,hvalue]
    exact hnegative

end SafeLearning.CompleteModulesGoSafeSamplingConsequences
