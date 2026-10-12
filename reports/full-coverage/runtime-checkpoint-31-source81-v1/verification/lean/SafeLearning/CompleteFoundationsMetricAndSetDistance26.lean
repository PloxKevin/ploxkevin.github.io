import Mathlib

namespace SafeLearning.CompleteFoundationsMetricAndSetDistance26

theorem actual_metric_axioms
    {D : Type*} [MetricSpace D] (x y z : D) :
    (dist x y = 0 ↔ x = y) ∧ dist x y = dist y x ∧
      dist x z ≤ dist x y + dist y z := by
  exact ⟨dist_eq_zero, dist_comm x y, dist_triangle x y z⟩

theorem actual_norm_induces_literal_metric
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖ := dist_eq_norm x y

theorem actual_closed_ball_is_literal_distance_sublevel
    {D : Type*} [PseudoMetricSpace D] (x : D) (r : ℝ) :
    Metric.closedBall x r = {y | dist x y ≤ r} := by
  ext y
  simp only [Metric.mem_closedBall, Set.mem_setOf_eq, dist_comm]

theorem actual_negative_radius_closed_ball_is_empty
    {D : Type*} [PseudoMetricSpace D] (x : D) (r : ℝ) (hr : r < 0) :
    Metric.closedBall x r = ∅ := Metric.closedBall_eq_empty.mpr hr

theorem actual_zero_radius_closed_ball_is_center_singleton
    {D : Type*} [MetricSpace D] (x : D) :
    Metric.closedBall x 0 = {x} := Metric.closedBall_zero

theorem actual_nonempty_norm_distance_values_are_nonempty_and_bounded_below
    {E : Type*} [NormedAddCommGroup E] (x : E) (C : Set E) (hC : C.Nonempty) :
    ((fun y => ‖x - y‖) '' C).Nonempty ∧
      BddBelow ((fun y => ‖x - y‖) '' C) := by
  refine ⟨hC.image _, ⟨0, ?_⟩⟩
  rintro v ⟨y, hy, rfl⟩
  exact norm_nonneg _

theorem actual_nonempty_distance_to_set_is_greatest_lower_bound_of_norm_values
    {E : Type*} [NormedAddCommGroup E] (x : E) (C : Set E) (hC : C.Nonempty) :
    IsGLB ((fun y => ‖x - y‖) '' C) (Metric.infDist x C) := by
  simpa only [dist_eq_norm] using (Metric.isGLB_infDist (x := x) hC)

theorem actual_nonempty_distance_to_set_is_literal_real_infimum
    {E : Type*} [NormedAddCommGroup E] (x : E) (C : Set E) (hC : C.Nonempty) :
    Metric.infDist x C = sInf ((fun y => ‖x - y‖) '' C) := by
  exact ((actual_nonempty_distance_to_set_is_greatest_lower_bound_of_norm_values x C hC).csInf_eq (hC.image _)).symm

end SafeLearning.CompleteFoundationsMetricAndSetDistance26
