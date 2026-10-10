import SafeLearning.CompleteAppliedCoverageScoreExperiment

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedCoverageSource
open CompleteAppliedCoverageOrderStatistic CompleteAppliedCoverageUniformLaw

theorem actual_source_calibration_rank_and_marginal_fraction :
    Nat.ceil (((19:ℝ)+1)*(1-1/10))=18 ∧ (18:ℝ)/20=9/10 := by
  norm_num

theorem actual_source_eighteenth_of_nineteen_is_an_actual_order_statistic
    (scores : Fin 19→ℝ) :
    (∃i:Fin 19,secondLargest scores=scores i) ∧
      ∀c:ℝ, secondLargest scores<c ↔
        (Finset.univ.filter (fun i:Fin 19=>scores i<c)).card=18 ∨
        (Finset.univ.filter (fun i:Fin 19=>scores i<c)).card=19 := by
  classical
  exact ⟨actual_second_largest_is_an_actual_coordinate scores,
    actual_second_largest_strict_threshold_is_at_least_eighteen_below scores⟩

end SafeLearning.CompleteAppliedCoverageSource
