import SafeLearning.CompleteModulesGoSafeFailSet
import SafeLearning.CompleteModulesGoSafeSamplingSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeCertifiedCoverage
open CompleteModulesGoSafeBackupGeometry CompleteModulesGoSafeBackupConsequences
open CompleteModulesGoSafeFiniteCertificates CompleteModulesGoSafeFailSet
open CompleteModulesGoSafeSamplingSafety

def actualCoverageCenter : Fin 3→ℝ := ![-3/20,1/2,1/5]
def actualCoverageLower (b : Fin 3) (_i : Fin 1) : ℝ := ![3/5,1/2,3/5] b

theorem actual_single_constraint_minimum_is_the_actual_lower_value (b : Fin 3) :
    actualFiniteMinimum (actualCoverageLower b)=actualCoverageLower b 0 := by
  apply le_antisymm
  · exact Finset.inf'_le _ (Finset.mem_univ (0:Fin 1))
  · apply (Finset.le_inf'_iff _ _).mpr
    intro i hi
    exact le_rfl

theorem actual_constant_backup_infimum_is_each_actual_state_margin (margin : ℝ→ℝ) (x : ℝ) :
    actualTrajectoryInfimum actualConstantBackup margin x=margin x := by
  unfold actualTrajectoryInfimum
  have hs : trajectoryMargins actualConstantBackup margin x={margin x} := by
    ext value
    constructor
    · rintro ⟨time,ht,h⟩
      exact h.symm
    · intro h
      exact ⟨0,by norm_num,h.symm⟩
  rw [hs];simp

theorem actual_margin_for_these_backup_trajectories_is_lipschitz_with_the_source_constant_two :
    LipschitzWith 2 (actualTrajectoryInfimum actualConstantBackup sourceMargin) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [actual_constant_backup_infimum_is_each_actual_state_margin,
    actual_constant_backup_infimum_is_each_actual_state_margin]
  simp only [Real.dist_eq,sourceMargin]
  rw [show (1-|x|)-(1-|y|)= -(|x|-|y|) by ring,abs_neg]
  have h := abs_abs_sub_abs_le_abs_sub x y
  norm_num at ⊢
  nlinarith [abs_nonneg (x-y)]

theorem actual_all_three_lower_bounds_are_true_backup_trajectory_certificates :
    ∀ b : Fin 3,actualCoverageLower b 0 ≤
      actualTrajectoryInfimum actualConstantBackup sourceMargin (actualCoverageCenter b) := by
  intro b
  rw [actual_constant_backup_infimum_is_each_actual_state_margin]
  fin_cases b <;> norm_num [actualCoverageLower,actualCoverageCenter,sourceMargin]

theorem actual_scalar_metric_radius_ball_is_its_literal_interval (center radius : ℝ) :
    {x : ℝ | dist x center ≤ radius}=Icc (center-radius) (center+radius) := by
  ext x
  simp only [Set.mem_setOf_eq,Real.dist_eq,abs_le,Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

def actualCoverageBall (b : Fin 3) : Set ℝ :=
  {x | dist x (actualCoverageCenter b) ≤ actualFiniteMinimum (actualCoverageLower b)/2-1/20}

theorem actual_the_three_certified_backup_balls_are_exactly_the_printed_old_balls_and_new_bridge :
    actualCoverageBall 0=Icc (-(2/5)) (1/10) ∧
      actualCoverageBall 1=Icc (3/10) (7/10) ∧
      actualCoverageBall 2=Icc (-(1/20)) (9/20) := by
  simp only [actualCoverageBall,actual_single_constraint_minimum_is_the_actual_lower_value,
    actual_scalar_metric_radius_ball_is_its_literal_interval]
  norm_num [actualCoverageCenter,actualCoverageLower]

theorem actual_old_library_union_is_the_actual_source_backup_union :
    certifiedStateUnion ({0,1}:Set (Fin 3)) actualCoverageCenter actualCoverageLower 2 (1/20)=
      sourceBackupUnion := by
  have hb := actual_the_three_certified_backup_balls_are_exactly_the_printed_old_balls_and_new_bridge
  ext x;constructor
  · rintro ⟨b,hb',hx⟩
    rcases hb' with rfl|hb'
    · exact Or.inl (by change x∈actualCoverageBall 0 at hx;rw [hb.1] at hx;exact hx)
    · have h : b=1 := hb'
      subst b
      exact Or.inr (by change x∈actualCoverageBall 1 at hx;rw [hb.2.1] at hx;exact hx)
  · rintro (hx|hx)
    · refine ⟨0,by simp,?_⟩
      change x∈actualCoverageBall 0
      rw [hb.1]
      exact hx
    · refine ⟨1,by simp,?_⟩
      change x∈actualCoverageBall 1
      rw [hb.2.1]
      exact hx

theorem actual_retaining_the_old_backups_and_adding_the_new_true_certificate_gives_exact_expanded_coverage :
    certifiedStateUnion (Set.univ : Set (Fin 3)) actualCoverageCenter actualCoverageLower 2 (1/20)=
      actualExpandedCoverage := by
  have hb := actual_the_three_certified_backup_balls_are_exactly_the_printed_old_balls_and_new_bridge
  ext x;constructor
  · rintro ⟨b,hb',hx⟩
    fin_cases b
    · change x∈actualCoverageBall 0 at hx;rw [hb.1] at hx
      exact ⟨hx.1,by linarith [hx.2]⟩
    · change x∈actualCoverageBall 1 at hx;rw [hb.2.1] at hx
      exact ⟨by linarith [hx.1],hx.2⟩
    · change x∈actualCoverageBall 2 at hx;rw [hb.2.2] at hx
      exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · intro hx
    by_cases hfirst : x ≤ (1/10:ℝ)
    · refine ⟨0,Set.mem_univ _,?_⟩
      change x∈actualCoverageBall 0
      rw [hb.1]
      exact ⟨hx.1,hfirst⟩
    · by_cases hsecond : (3/10:ℝ) ≤ x
      · refine ⟨1,Set.mem_univ _,?_⟩
        change x∈actualCoverageBall 1
        rw [hb.2.1]
        exact ⟨hsecond,hx.2⟩
      · refine ⟨2,Set.mem_univ _,?_⟩
        change x∈actualCoverageBall 2
        rw [hb.2.2]
        constructor <;> linarith

end SafeLearning.CompleteModulesGoSafeCertifiedCoverage
