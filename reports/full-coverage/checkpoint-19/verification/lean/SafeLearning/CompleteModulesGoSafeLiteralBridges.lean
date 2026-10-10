import SafeLearning.CompleteModulesGoSafeBackupGeometry
import SafeLearning.CompleteModulesGoSafeBackupConsequences
import SafeLearning.CompleteModulesGoSafeFiniteCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeLiteralBridges
open CompleteModulesGoSafeBackupGeometry CompleteModulesGoSafeBackupConsequences

theorem actual_every_printed_individual_sample_margin :
    (1-|sourceSamplePath 0|,(1-|sourceSamplePath 1|),(1-|sourceSamplePath 2|),(1-|sourceSamplePath 3|))=
      ((1:ℝ),7/10,1/10,3/5) := by
  norm_num [sourceSamplePath]

theorem actual_lipschitz_backup_certificate_has_the_literal_quantitative_transferred_margin
    {X : Type*} [PseudoMetricSpace X] (g : X→ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) (stored current activation : X) (lower motion : ℝ)
    (hstored : lower ≤ g stored) (hmove : dist activation current ≤ motion) :
    lower-(L:ℝ)*(dist current stored+motion) ≤ g activation := by
  have hd := hg.dist_le_mul activation stored
  have ht := dist_triangle activation current stored
  have hb : (L:ℝ)*dist activation stored ≤ (L:ℝ)*(dist current stored+motion) := by
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    linarith
  rw [Real.dist_eq] at hd
  have ha := (abs_le.mp hd).1
  linarith

theorem actual_source_backup_point_four_has_point_one_as_its_guaranteed_margin
    (g : ℝ→ℝ) (hg : LipschitzWith 2 g) (activation : ℝ)
    (hstored : (3/5:ℝ) ≤ g (1/5)) (hmove : dist activation (2/5) ≤ (1/20:ℝ)) :
    (1/10:ℝ) ≤ g activation := by
  have h := actual_lipschitz_backup_certificate_has_the_literal_quantitative_transferred_margin
    g 2 hg (1/5) (2/5) activation (3/5) (1/20) hstored hmove
  norm_num [Real.dist_eq] at h ⊢
  exact h

theorem actual_restarted_trajectory_margin_set_is_exactly_the_original_suffix
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ) (ht : 0 ≤ time) :
    trajectoryMargins F margin (F.path time x)=
      (fun t : ℝ=>margin (F.path t x)) '' Ici time := by
  ext value;constructor
  · rintro ⟨s,hs,rfl⟩
    refine ⟨time+s,show time ≤ time+s from by change 0 ≤ s at hs;linarith,?_⟩
    change margin (F.path (time+s) x)=margin (F.path s (F.path time x))
    rw [F.restart time s x ht hs]
  · rintro ⟨t,htime,rfl⟩
    have htt : time ≤ t := htime
    refine ⟨t-time,show 0 ≤ t-time from sub_nonneg.mpr htt,?_⟩
    change margin (F.path (t-time) (F.path time x))=margin (F.path t x)
    rw [F.restart time (t-time) x ht (sub_nonneg.mpr htt)]
    congr 2
    ring

theorem actual_restarted_infimum_is_the_literal_source_suffix_infimum
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (x : X) (time : ℝ) (ht : 0 ≤ time) :
    actualTrajectoryInfimum F margin (F.path time x)=
      sInf ((fun t : ℝ=>margin (F.path t x)) '' Ici time) := by
  unfold actualTrajectoryInfimum
  rw [actual_restarted_trajectory_margin_set_is_exactly_the_original_suffix F margin x time ht]

theorem actual_nonnegative_real_trajectory_infimum_certifies_every_future_time
    {X : Type*} (F : ClosedLoop X) (margin : X→ℝ) (activation : X)
    (hbounded : BddBelow (trajectoryMargins F margin activation))
    (hinfimum : 0 ≤ actualTrajectoryInfimum F margin activation) :
    ∀ time : ℝ,0 ≤ time→0 ≤ margin (F.path time activation) := by
  intro time ht
  apply hinfimum.trans
  exact csInf_le hbounded ⟨time,ht,rfl⟩

theorem actual_finite_backup_minimum_certifies_every_time_of_every_backup_constraint
    {X ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (F : ClosedLoop X) (margin : ι→X→ℝ) (L : ℝ≥0)
    (hg : ∀ i,LipschitzWith L (actualTrajectoryInfimum F (margin i)))
    (stored current activation : X) (lower : ι→ℝ) (motion : ℝ)
    (hstored : ∀ i,lower i ≤ actualTrajectoryInfimum F (margin i) stored)
    (hmove : dist activation current ≤ motion)
    (hcertificate : (L:ℝ)*(dist current stored+motion) ≤
      CompleteModulesGoSafeFiniteCertificates.actualFiniteMinimum lower)
    (hbounded : ∀ i,BddBelow (trajectoryMargins F (margin i) activation)) :
    ∀ i,∀ time : ℝ,0 ≤ time→0 ≤ margin i (F.path time activation) := by
  have hall := CompleteModulesGoSafeFiniteCertificates.actual_finite_minimum_transfers_the_one_backup_condition_to_every_constraint
    (fun i=>actualTrajectoryInfimum F (margin i)) L hg stored current activation lower motion
    hstored hmove hcertificate
  intro i
  exact actual_nonnegative_real_trajectory_infimum_certifies_every_future_time
    F (margin i) activation (hbounded i) (hall i)

end SafeLearning.CompleteModulesGoSafeLiteralBridges
