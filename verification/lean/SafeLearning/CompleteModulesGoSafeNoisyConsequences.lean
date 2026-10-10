import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory BigOperators
namespace SafeLearning.CompleteModulesGoSafeNoisyConsequences

theorem actual_backup_inequality_defines_the_literal_closed_ball_radius
    {X : Type*} [PseudoMetricSpace X] (x stored : X) (lower motion : ℝ) :
    lower ≥ 2*(dist x stored+motion) ↔ dist x stored ≤ lower/2-motion := by
  constructor <;> intro h <;> linarith

theorem actual_first_and_second_source_conditions_are_membership_in_the_radius_point_two_and_point_one_balls
    {X : Type*} [PseudoMetricSpace X] (x first second : X) :
    ((1/2:ℝ) ≥ 2*(dist x first+1/20) ↔ x ∈ Metric.closedBall first (1/5)) ∧
      ((3/10:ℝ) ≥ 2*(dist x second+1/20) ↔ x ∈ Metric.closedBall second (1/10)) := by
  constructor <;> rw [actual_backup_inequality_defines_the_literal_closed_ball_radius]
  · norm_num [Metric.mem_closedBall]
  · norm_num [Metric.mem_closedBall]

theorem actual_noisy_source_conditions_are_membership_in_the_radius_point_one_eight_and_point_zero_eight_balls
    {X : Type*} [PseudoMetricSpace X] (x first second : X) :
    ((1/2:ℝ) ≥ 2*(dist x first+7/100) ↔ x ∈ Metric.closedBall first (9/50)) ∧
      ((3/10:ℝ) ≥ 2*(dist x second+7/100) ↔ x ∈ Metric.closedBall second (2/25)) := by
  constructor <;> rw [actual_backup_inequality_defines_the_literal_closed_ball_radius]
  · norm_num [Metric.mem_closedBall]
  · norm_num [Metric.mem_closedBall]

theorem actual_two_error_reverse_triangle_difference_has_the_literal_bound
    {X : Type*} [PseudoMetricSpace X] (x stored measured measuredStored : X) :
    dist x stored-dist measured measuredStored ≤ dist x measured+dist stored measuredStored := by
  have h1 := dist_triangle x measured stored
  have h2 := dist_triangle measured measuredStored stored
  rw [dist_comm measuredStored stored] at h2
  linarith

theorem actual_finite_run_comparisons_and_the_gp_good_event_need_their_combined_failure_budget
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (gpGood : Set Ω)
    (comparisonGood : ι → Set Ω) (deltaGP deltaComparison : ℝ)
    (hgpmeas : MeasurableSet gpGood) (hmeas : ∀ i, MeasurableSet (comparisonGood i))
    (hgp : 1-deltaGP ≤ μ.real gpGood)
    (hcomp : ∀ i, 1-deltaComparison ≤ μ.real (comparisonGood i)) :
    1-deltaGP-(Fintype.card ι:ℝ)*deltaComparison ≤ μ.real (gpGood∩⋂ i,comparisonGood i) := by
  let failures : Option ι → Set Ω := fun i => match i with
    | none => gpGoodᶜ
    | some i => (comparisonGood i)ᶜ
  let budgets : Option ι → ℝ := fun i => match i with
    | none => deltaGP
    | some _ => deltaComparison
  have hfmeas : ∀ i, MeasurableSet (failures i) := by
    intro i
    cases i with
    | none => exact hgpmeas.compl
    | some i => exact (hmeas i).compl
  have hfprob : ∀ i, μ.real (failures i) ≤ budgets i := by
    intro i
    cases i with
    | none =>
      change μ.real gpGoodᶜ ≤ deltaGP
      rw [probReal_compl_eq_one_sub hgpmeas]
      linarith
    | some i =>
      change μ.real (comparisonGood i)ᶜ ≤ deltaComparison
      rw [probReal_compl_eq_one_sub (hmeas i)]
      linarith [hcomp i]
  have h := SafeLearning.CompleteModulesTheory.simultaneous_success μ failures budgets hfmeas hfprob
  simpa [failures,budgets,Fintype.sum_option,Set.iInter_option,sub_sub] using h

end SafeLearning.CompleteModulesGoSafeNoisyConsequences
