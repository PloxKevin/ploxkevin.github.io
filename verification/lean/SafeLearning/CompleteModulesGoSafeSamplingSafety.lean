import SafeLearning.CompleteModulesGoSafeLiteralBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeSamplingSafety
open CompleteModulesGoSafeBackupConsequences CompleteModulesGoSafeLiteralBridges

theorem actual_positive_sample_period_parameterizes_every_time_before_the_next_sample
    (sample period time : ℝ) (hp : 0<period)
    (ht : time∈Icc sample (sample+period)) :
    ∃ rho∈Icc (0:ℝ) 1,time=sample+rho*period := by
  refine ⟨(time-sample)/period,?_,?_⟩
  · constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hp.le
    · apply (div_le_one hp).mpr
      linarith [ht.2]
  · field_simp
    ring

theorem actual_each_sample_margin_transfers_to_every_time_in_the_interval
    {X : Type*} [PseudoMetricSpace X] (g : X→ℝ) (L : ℝ≥0) (hg : LipschitzWith L g)
    (path : ℝ→X) (sample period motion : ℝ)
    (hmove : ∀ time∈Icc sample (sample+period),dist (path time) (path sample) ≤ motion) :
    ∀ time∈Icc sample (sample+period),g (path sample)-(L:ℝ)*motion ≤ g (path time) := by
  intro time ht
  have h := actual_lipschitz_backup_certificate_has_the_literal_quantitative_transferred_margin
    g L hg (path sample) (path sample) (path time) (g (path sample)) motion le_rfl (hmove time ht)
  simpa using h

theorem actual_nonnegative_sample_margin_covers_every_interval_state_constraint
    {X : Type*} [PseudoMetricSpace X] (F : ClosedLoop X) (margin : X→ℝ)
    (L : ℝ≥0) (hg : LipschitzWith L (actualTrajectoryInfimum F margin))
    (path : ℝ→X) (sample period motion : ℝ)
    (hmove : ∀ time∈Icc sample (sample+period),dist (path time) (path sample) ≤ motion)
    (hsample : (L:ℝ)*motion ≤ actualTrajectoryInfimum F margin (path sample))
    (hbounded : ∀ time∈Icc sample (sample+period),BddBelow (trajectoryMargins F margin (path time))) :
    ∀ time∈Icc sample (sample+period),0 ≤ margin (path time) := by
  intro time ht
  have h := actual_each_sample_margin_transfers_to_every_time_in_the_interval
    (actualTrajectoryInfimum F margin) L hg path sample period motion hmove time ht
  have hinf : 0 ≤ actualTrajectoryInfimum F margin (path time) := by linarith
  have hall := actual_nonnegative_real_trajectory_infimum_certifies_every_future_time
    F margin (path time) (hbounded time ht) hinf 0 (by norm_num)
  simpa only [F.start] using hall

theorem actual_previous_sample_backup_remains_nonnegative_at_the_trigger_sample
    {X : Type*} [PseudoMetricSpace X] (g : X→ℝ) (L : ℝ≥0) (hg : LipschitzWith L g)
    (stored previous trigger : X) (lower motion : ℝ)
    (hlower : lower ≤ g stored) (hmove : dist trigger previous ≤ motion)
    (hprevious : (L:ℝ)*(dist previous stored+motion) ≤ lower) :
    lower-(L:ℝ)*dist trigger stored ≤ g trigger ∧
      lower-(L:ℝ)*(dist previous stored+motion) ≤
        lower-(L:ℝ)*dist trigger stored ∧
      0 ≤ g trigger := by
  have hquant := actual_lipschitz_backup_certificate_has_the_literal_quantitative_transferred_margin
    g L hg stored trigger trigger lower 0 hlower (by simp)
  simp only [add_zero] at hquant
  have htriangle := dist_triangle trigger previous stored
  have hdist : (L:ℝ)*dist trigger stored ≤ (L:ℝ)*(dist previous stored+motion) := by
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    linarith
  refine ⟨hquant,by linarith,by linarith⟩

def actualConstantBackup : ClosedLoop ℝ where
  path := fun _time x=>x
  start := fun _=>rfl
  restart := fun _ _ _ _ _=>rfl

def sourceUnsafeMargin (x : ℝ) : ℝ := -2*x

theorem actual_constant_backup_trajectory_minimum_is_the_literal_state_margin (x : ℝ) :
    actualTrajectoryInfimum actualConstantBackup sourceUnsafeMargin x=sourceUnsafeMargin x := by
  unfold actualTrajectoryInfimum
  have hs : trajectoryMargins actualConstantBackup sourceUnsafeMargin x={sourceUnsafeMargin x} := by
    ext value
    simp only [trajectoryMargins,actualConstantBackup,Set.mem_image,Set.mem_Ici,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨t,ht,h⟩;exact h.symm
    · intro h;exact ⟨0,by norm_num,h.symm⟩
  rw [hs];simp

theorem actual_counterexample_margin_has_exact_source_lipschitz_constant_two :
    LipschitzWith 2 sourceUnsafeMargin := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [sourceUnsafeMargin,Real.dist_eq]
  rw [show -2*x-(-2*y)=(-2)*(x-y) by ring,abs_mul]
  norm_num

theorem actual_omitting_motion_tolerance_can_pass_the_old_test_and_already_be_unsafe :
    (0:ℝ) ≥ 2*dist (0:ℝ) 0 ∧
      dist (1/20:ℝ) 0=1/20 ∧
      actualTrajectoryInfimum actualConstantBackup sourceUnsafeMargin 0=0 ∧
      actualTrajectoryInfimum actualConstantBackup sourceUnsafeMargin (1/20)= -1/10 ∧
      ¬((0:ℝ) ≥ 2*(dist (0:ℝ) 0+1/20)) := by
  rw [actual_constant_backup_trajectory_minimum_is_the_literal_state_margin,
    actual_constant_backup_trajectory_minimum_is_the_literal_state_margin]
  norm_num [sourceUnsafeMargin,Real.dist_eq]

end SafeLearning.CompleteModulesGoSafeSamplingSafety
