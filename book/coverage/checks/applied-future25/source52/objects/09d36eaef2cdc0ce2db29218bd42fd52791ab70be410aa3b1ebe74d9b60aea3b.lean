import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeBackupConsequences

theorem actual_lipschitz_backup_certificate_covers_every_possible_activation
    {X : Type*} [PseudoMetricSpace X] (g : X→ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) (stored current activation : X) (lower motion : ℝ)
    (hstored : lower ≤ g stored) (hmove : dist activation current ≤ motion)
    (hcertificate : (L:ℝ)*(dist current stored+motion) ≤ lower) :
    0 ≤ g activation := by
  have hgdist := hg.dist_le_mul activation stored
  have htriangle := dist_triangle activation current stored
  have hbound : (L:ℝ)*dist activation stored ≤ lower := by
    calc
      _ ≤ (L:ℝ)*(dist current stored+motion) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        linarith
      _ ≤ lower := hcertificate
  rw [Real.dist_eq] at hgdist
  have habs := (abs_le.mp hgdist).1
  linarith

/-- The closed-loop flow encodes the complete autonomous Markov state and its restart law. -/
structure ClosedLoop (X : Type*) where
  path : ℝ→X→X
  start : ∀ x,path 0 x=x
  restart : ∀ t s x,0 ≤ t→0 ≤ s→path s (path t x)=path (t+s) x

def trajectoryMargins {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) : Set ℝ :=
  (fun time : ℝ=>margin (F.path time x)) '' Ici 0
def actualTrajectoryInfimum {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) : ℝ :=
  sInf (trajectoryMargins F margin x)

theorem actual_whole_trajectory_margin_set_is_nonempty {X : Type*}
    (F : ClosedLoop X) (margin : X→ℝ) (x : X) :
    (trajectoryMargins F margin x).Nonempty :=
  ⟨margin x,0,by simp,by change margin (F.path 0 x)=margin x;rw [F.start]⟩

theorem actual_restarted_trajectory_is_a_suffix_of_the_same_complete_closed_loop
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ) (ht : 0 ≤ time) :
    trajectoryMargins F margin (F.path time x)⊆trajectoryMargins F margin x := by
  rintro value ⟨s,hs,rfl⟩
  refine ⟨time+s,add_nonneg ht hs,?_⟩
  change margin (F.path (time+s) x)=margin (F.path s (F.path time x))
  rw [F.restart time s x ht hs]

theorem actual_infimum_of_the_restarted_trajectory_cannot_be_smaller
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ) (ht : 0 ≤ time)
    (hbounded : BddBelow (trajectoryMargins F margin x)) :
    actualTrajectoryInfimum F margin x ≤ actualTrajectoryInfimum F margin (F.path time x) := by
  apply le_csInf (actual_whole_trajectory_margin_set_is_nonempty F margin _)
  intro value hv
  exact csInf_le hbounded
    (actual_restarted_trajectory_is_a_suffix_of_the_same_complete_closed_loop F margin x time ht hv)

theorem actual_source_point_two_margin_is_retained_at_every_visited_state
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ) (ht : 0 ≤ time)
    (hbounded : BddBelow (trajectoryMargins F margin x))
    (hmargin : (1/5:ℝ) ≤ actualTrajectoryInfimum F margin x) :
    (1/5:ℝ) ≤ actualTrajectoryInfimum F margin (F.path time x) :=
  hmargin.trans (actual_infimum_of_the_restarted_trajectory_cannot_be_smaller F margin x time ht hbounded)

end SafeLearning.CompleteModulesGoSafeBackupConsequences
