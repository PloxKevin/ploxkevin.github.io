import SafeLearning.CompleteModulesGoSafeDiscovery
import SafeLearning.CompleteModulesGoSafeFiniteCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeFailSet
open CompleteModulesGoSafeBackupGeometry CompleteModulesGoSafeDiscovery
open CompleteModulesGoSafeFiniteCertificates

theorem actual_intersecting_the_confidence_interval_with_nonnegative_values_updates_its_lower_endpoint
    (lower upper : ℝ) : Icc lower upper∩Ici (0:ℝ)=Icc (max lower 0) upper := by
  ext x
  simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ici,max_le_iff]
  tauto

theorem actual_pointwise_confidence_and_successful_experiment_updates_preserve_lower_bounds
    {ι : Type*} (old mean sigma : ι→ℝ) (beta : ℝ) :
    (∀ i,old i ≤ max (old i) (mean i-beta*sigma i)) ∧
      (∀ i,old i ≤ max (old i) 0) :=
  ⟨fun i=>le_max_left _ _,fun i=>le_max_left _ _⟩

theorem actual_finite_minimum_is_monotone_under_every_pointwise_lower_update
    {ι : Type*} [Fintype ι] [Nonempty ι] (old new : ι→ℝ)
    (h : ∀ i,old i ≤ new i) : actualFiniteMinimum old ≤ actualFiniteMinimum new := by
  apply (Finset.le_inf'_iff _ _).mpr
  intro i hi
  exact (Finset.inf'_le old hi).trans (h i)

theorem actual_both_literal_lower_updates_preserve_the_finite_constraint_minimum
    {ι : Type*} [Fintype ι] [Nonempty ι] (old mean sigma : ι→ℝ) (beta : ℝ) :
    actualFiniteMinimum old ≤ actualFiniteMinimum (fun i=>max (old i) (mean i-beta*sigma i)) ∧
      actualFiniteMinimum old ≤ actualFiniteMinimum (fun i=>max (old i) 0) := by
  exact ⟨actual_finite_minimum_is_monotone_under_every_pointwise_lower_update _ _ (fun i=>le_max_left _ _),
    actual_finite_minimum_is_monotone_under_every_pointwise_lower_update _ _ (fun i=>le_max_left _ _)⟩

theorem actual_each_old_backup_witness_survives_both_literal_lower_update_rules
    {X κ ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (oldBackups newBackups : Set κ) (center : κ→X)
    (old mean sigma : κ→ι→ℝ) (beta L motion : ℝ)
    (hL : 0<L) (hretained : oldBackups⊆newBackups) :
    certifiedStateUnion oldBackups center old L motion⊆
      certifiedStateUnion newBackups center (fun b i=>max (old b i) (mean b i-beta*sigma b i)) L motion ∧
    certifiedStateUnion oldBackups center old L motion⊆
      certifiedStateUnion newBackups center (fun b i=>max (old b i) 0) L motion := by
  constructor <;>
    apply actual_retained_backups_and_pointwise_increasing_lower_bounds_grow_the_full_state_union
      oldBackups newBackups center old _ L motion hL hretained <;>
    intro b hb i <;> exact le_max_left _ _

def actualExpandedCoverage : Set ℝ := Icc (-(2/5)) (7/10)
def actualInterruptedState (parameter : Bool) : ℝ := sourceIslandPath parameter (4/5)

def actualRecheckedExclusion (excluded : Set Bool) (coverage : Set ℝ) : Set Bool :=
  {p | p∈excluded ∧ actualInterruptedState p∉coverage}

def actualAcquisitionDomain (coverage : Set ℝ) (excluded : Set Bool) : Set Bool :=
  {p | (∀ time : ℝ,0 ≤ time→sourceIslandPath p time∈coverage) ∧ p∉excluded}

theorem actual_new_coverage_contains_the_old_coverage_and_is_physically_safe :
    sourceBackupUnion⊆actualExpandedCoverage ∧
      ∀ x∈actualExpandedCoverage,0 ≤ (1:ℝ)-|x| := by
  constructor
  · exact actual_backup_union_covers_only_the_printed_witnesses_and_retains_its_gap.2.2.2.1
  · intro x hx
    have hl : -(2/5:ℝ) ≤ x := hx.1
    have hu : x ≤ (7/10:ℝ) := hx.2
    have ha : |x|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    linarith

theorem actual_each_physically_safe_parameter_can_complete_with_the_new_coverage (p : Bool) :
    ∀ time : ℝ,0 ≤ time→sourceIslandPath p time∈actualExpandedCoverage := by
  intro time ht
  cases p with
  | false => norm_num [sourceIslandPath,actualExpandedCoverage]
  | true =>
    have hmin : 0 ≤ min (max time 0) 2 := le_min (le_max_right _ _) (by norm_num)
    have hmax : min (max time 0) 2 ≤ 2 := min_le_right _ _
    change -(2/5:ℝ) ≤ min (max time 0) 2/4 ∧ min (max time 0) 2/4 ≤ 7/10
    constructor <;> linarith

theorem actual_original_interruption_does_not_mean_the_parameter_is_physically_unsafe :
    actualInterruptedState true∉sourceBackupUnion ∧
      0 ≤ (1:ℝ)-|actualInterruptedState true| ∧
      actualInterruptedState true∈actualExpandedCoverage ∧
      (∀ time : ℝ,0 ≤ (1:ℝ)-|sourceIslandPath true time|) := by
  refine ⟨?_,?_,?_,actual_both_island_paths_are_continuous_and_physically_safe true |>.2⟩
  · norm_num [actualInterruptedState,sourceIslandPath,sourceBackupUnion]
  · norm_num [actualInterruptedState,sourceIslandPath]
  · norm_num [actualInterruptedState,sourceIslandPath,actualExpandedCoverage]

theorem actual_rechecking_the_newly_certified_interrupted_state_removes_its_exclusion :
    actualRecheckedExclusion {true} actualExpandedCoverage=∅ := by
  ext p
  cases p <;> norm_num [actualRecheckedExclusion,actualInterruptedState,sourceIslandPath,actualExpandedCoverage]

theorem actual_permanent_exclusion_and_rechecked_acquisition_domains_are_different :
    actualAcquisitionDomain actualExpandedCoverage {true}={false} ∧
      actualAcquisitionDomain actualExpandedCoverage
        (actualRecheckedExclusion {true} actualExpandedCoverage)=Set.univ := by
  constructor
  · ext p
    cases p with
    | false =>
      simpa [actualAcquisitionDomain] using
        actual_each_physically_safe_parameter_can_complete_with_the_new_coverage false
    | true => simp [actualAcquisitionDomain]
  · rw [actual_rechecking_the_newly_certified_interrupted_state_removes_its_exclusion]
    ext p
    simp only [actualAcquisitionDomain,Set.mem_setOf_eq,Set.mem_empty_iff_false,not_false_eq_true,
      and_true,Set.mem_univ,iff_true]
    exact actual_each_physically_safe_parameter_can_complete_with_the_new_coverage p

theorem actual_permanent_exclusion_locks_out_the_newly_certified_global_optimum :
    IsGreatest {value : ℝ | ∃ p,p∈actualAcquisitionDomain actualExpandedCoverage {true} ∧
      sourceIslandValue p=value} 1 ∧
      IsGreatest {value : ℝ | ∃ p,p∈actualAcquisitionDomain actualExpandedCoverage
        (actualRecheckedExclusion {true} actualExpandedCoverage) ∧ sourceIslandValue p=value} 3 ∧
      (1:ℝ)<3 := by
  rw [actual_permanent_exclusion_and_rechecked_acquisition_domains_are_different.1,
    actual_permanent_exclusion_and_rechecked_acquisition_domains_are_different.2]
  constructor
  · constructor
    · exact ⟨false,by simp,by norm_num [sourceIslandValue]⟩
    · rintro value ⟨p,hp,rfl⟩
      have he : p=false := hp
      rw [he];norm_num [sourceIslandValue]
  constructor
  · constructor
    · exact ⟨true,by simp,by norm_num [sourceIslandValue]⟩
    · rintro value ⟨p,hp,rfl⟩
      cases p <;> norm_num [sourceIslandValue]
  · norm_num

end SafeLearning.CompleteModulesGoSafeFailSet
