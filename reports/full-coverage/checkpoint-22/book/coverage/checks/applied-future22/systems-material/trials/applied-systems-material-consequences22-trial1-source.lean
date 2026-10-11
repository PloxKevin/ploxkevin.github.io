import SafeLearning.CompleteAppliedSystemsMaterial22

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSystemsMaterialConsequences22
open SafeLearning.CompleteAppliedSystemsMaterial22

theorem actual_zero_target_temperature_rate_iff_input_is_one (input : ℝ) :
    -((22:ℝ)-18)/20+(1/5)*input=0 ↔ input=1 := by
  constructor <;> intro h <;> linarith

theorem actual_continuous_feedback_input_equality_iff_error_equality
    (firstError secondError : ℝ) :
    (-(firstError/2)=-(secondError/2) ↔ firstError=secondError) ∧
    (1-firstError/2=1-secondError/2 ↔ firstError=secondError) := by
  constructor <;> constructor <;> intro h <;> linarith

theorem actual_nonzero_continuous_thermal_error_and_input_change_after_positive_time
    (initial time : ℝ) (hinitial : initial ≠ 0) (htime : 0 < time) :
    actualContinuousThermal initial time ≠ initial ∧
    -(actualContinuousThermal initial time/2) ≠ -(initial/2) ∧
    1-actualContinuousThermal initial time/2 ≠ 1-initial/2 := by
  have he : Real.exp (-(3/20:ℝ)*time) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith
  have hs : actualContinuousThermal initial time ≠ initial := by
    intro h
    have hm : Real.exp (-(3/20:ℝ)*time)*initial=1*initial := by
      simpa only [actualContinuousThermal,one_mul] using h
    exact he.ne ((mul_right_inj' hinitial).mp hm)
  refine ⟨hs,?_,?_⟩
  · intro h
    exact hs ((actual_continuous_feedback_input_equality_iff_error_equality
      (actualContinuousThermal initial time) initial).1.mp h)
  · intro h
    exact hs ((actual_continuous_feedback_input_equality_iff_error_equality
      (actualContinuousThermal initial time) initial).2.mp h)

end SafeLearning.CompleteAppliedSystemsMaterialConsequences22
