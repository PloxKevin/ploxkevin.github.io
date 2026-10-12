import SafeLearning.CompleteModulesGoSafeBackupGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeDiscovery
open CompleteModulesGoSafeBackupGeometry

/-- Two physically safe experiments; the second passes through the uncertified gap. -/
def sourceIslandPath (parameter : Bool) (time : ℝ) : ℝ :=
  if parameter then min (max time 0) 2/4 else 0

def sourceIslandValue (parameter : Bool) : ℝ := if parameter then 3 else 1

def sourceIslandCompletesUnderKnownCoverage (parameter : Bool) : Prop :=
  ∀ time : ℝ,0 ≤ time→sourceIslandPath parameter time∈sourceBackupUnion

theorem actual_both_island_paths_are_continuous_and_physically_safe (parameter : Bool) :
    Continuous (sourceIslandPath parameter) ∧
      ∀ time : ℝ,0 ≤ (1:ℝ)-|sourceIslandPath parameter time| := by
  cases parameter with
  | false =>
    constructor
    · change Continuous (fun _time : ℝ=>(0:ℝ));exact continuous_const
    · intro time;norm_num [sourceIslandPath]
  | true =>
    constructor
    · change Continuous (fun time : ℝ=>min (max time 0) 2/4);fun_prop
    · intro time
      have hmin : 0 ≤ min (max time 0) 2 := le_min (le_max_right _ _) (by norm_num)
      have hmax : min (max time 0) 2 ≤ 2 := min_le_right _ _
      have hl : 0 ≤ min (max time 0) 2/4 := div_nonneg hmin (by norm_num)
      have hu : min (max time 0) 2/4 ≤ (1/2:ℝ) := by linarith
      simp only [sourceIslandPath,Bool.true_eq_false,if_false,if_true]
      rw [abs_of_nonneg hl]
      linarith

theorem actual_only_the_seed_island_can_complete_with_the_known_backup_coverage
    (parameter : Bool) : sourceIslandCompletesUnderKnownCoverage parameter ↔ parameter=false := by
  cases parameter with
  | false => norm_num [sourceIslandCompletesUnderKnownCoverage,sourceIslandPath,sourceBackupUnion]
  | true =>
    simp only [Bool.true_eq_false,iff_false]
    intro h
    have hh := h (4/5) (by norm_num)
    norm_num [sourceIslandPath,sourceBackupUnion] at hh

theorem actual_the_second_island_has_an_uncertified_intermediate_state :
    sourceIslandPath true 0=0 ∧ sourceIslandPath true (4/5)=1/5 ∧
      sourceIslandPath true 2=1/2 ∧ (1/5:ℝ)∉sourceBackupUnion := by
  norm_num [sourceIslandPath,sourceBackupUnion]

theorem actual_safety_and_known_coverage_do_not_imply_the_safe_global_value_three :
    IsGreatest {value : ℝ | ∃ parameter,sourceIslandValue parameter=value} 3 ∧
      IsGreatest {value : ℝ | ∃ parameter,
        sourceIslandCompletesUnderKnownCoverage parameter ∧ sourceIslandValue parameter=value} 1 ∧
      (1:ℝ)<3 := by
  constructor
  · constructor
    · exact ⟨true,by simp [sourceIslandValue]⟩
    · rintro value ⟨parameter,rfl⟩
      cases parameter <;> norm_num [sourceIslandValue]
  constructor
  · constructor
    · refine ⟨false,?_,by simp [sourceIslandValue]⟩
      exact (actual_only_the_seed_island_can_complete_with_the_known_backup_coverage false).mpr rfl
    · rintro value ⟨parameter,hcovered,rfl⟩
      have hp := (actual_only_the_seed_island_can_complete_with_the_known_backup_coverage parameter).mp hcovered
      rw [hp];simp [sourceIslandValue]
  · norm_num

end SafeLearning.CompleteModulesGoSafeDiscovery
