import SafeLearning.CompleteBarrierDiscontinuousSign

set_option autoImplicit false
noncomputable section
open Set Metric
namespace SafeLearning.CompleteBarrierDegenerateControl

/-- The source sign convention gives a genuinely discontinuous, measurable
controller; this is not merely a chosen name for a discontinuous function. -/
theorem genuine_controller_discontinuous :
    ¬ContinuousAt CompleteBarrierDiscontinuousSign.field 0 := by
  intro h
  obtain ⟨delta, hd, hn⟩ := Metric.continuousAt_iff.mp h 1 (by norm_num)
  have hneg : -(delta / 2) < 0 := by linarith
  have hnear : dist (-(delta / 2)) (0 : ℝ) < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hneg]
    linarith
  have hbad := hn hnear
  simp [CompleteBarrierDiscontinuousSign.field, hneg, Real.dist_eq] at hbad
  norm_num at hbad

/-- A zero control direction annihilates the controller's jump. Both f and g
are locally Lipschitz, while the actual closed-loop field is identically zero. -/
theorem genuine_discontinuous_controller_continuous_closed_loop :
    Measurable CompleteBarrierDiscontinuousSign.field ∧
    ¬ContinuousAt CompleteBarrierDiscontinuousSign.field 0 ∧
    Continuous (fun x : ℝ => 0 + 0 * CompleteBarrierDiscontinuousSign.field x) ∧
    ∀ x : ℝ, 0 + 0 * CompleteBarrierDiscontinuousSign.field x = 0 := by
  refine ⟨CompleteBarrierDiscontinuousSign.genuine_measurable_field,
    genuine_controller_discontinuous, ?_, ?_⟩
  · simpa using continuous_const (y := (0 : ℝ))
  · intro x
    ring

end SafeLearning.CompleteBarrierDegenerateControl
