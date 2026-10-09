import SafeLearning.CompleteBarrierDegenerateControl

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteBarrierDegenerateCBF

/-- The vanishing-control-direction counterexample also meets the actual CBF
settings: h=1, f=g=0, every input is admissible, and the safe set is all states. -/
theorem genuine_degenerate_cbf_witness (beta : ℝ) (hb : 0 < beta) :
    LipschitzWith 0 (fun _ : ℝ => (0 : ℝ)) ∧
    ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) ∧
    (∀ x : ℝ, HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x) ∧
    (∀ x : ℝ, -beta * 1 ≤
      0 * 0 + 0 * 0 * CompleteBarrierDiscontinuousSign.field x) ∧
    {x : ℝ | 0 ≤ (fun _ : ℝ => (1 : ℝ)) x} = univ ∧
    Measurable CompleteBarrierDiscontinuousSign.field ∧
    ¬ContinuousAt CompleteBarrierDiscontinuousSign.field 0 ∧
    Continuous (fun x : ℝ => 0 + 0 * CompleteBarrierDiscontinuousSign.field x) := by
  refine ⟨LipschitzWith.const 0, by fun_prop, fun x => hasDerivAt_const x 1,
    ?_, by simp, CompleteBarrierDiscontinuousSign.genuine_measurable_field,
    CompleteBarrierDegenerateControl.genuine_controller_discontinuous, ?_⟩
  · intro x
    simp only [mul_zero, zero_mul, add_zero, mul_one]
    linarith
  · simpa using continuous_const (y := (0 : ℝ))

end SafeLearning.CompleteBarrierDegenerateCBF
