import SafeLearning.CompleteAppliedFiniteHorizonQuadratic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteHorizonSourceConsequences
open SafeLearning.CompleteAppliedFiniteHorizonQuadratic

theorem actual_source_one_step_cost_polynomial_and_two_derivatives (input : ℝ) :
    finalStepCost 2 input=2*input^2+4*input+4 ∧
    HasDerivAt (finalStepCost 2) (4*input+4) input ∧
    HasDerivAt (fun u : ℝ => 4*u+4) 4 input ∧ (0:ℝ)<4 := by
  have hd := actual_final_step_derivative_and_positive_second_derivative 2 input
  refine ⟨?_,?_,?_,by norm_num⟩
  · simp only [finalStepCost,nextState];ring
  · convert hd.1 using 1 <;> ring
  · convert hd.2 using 1 <;> norm_num

theorem actual_source_two_step_first_cost_polynomial_and_derivative (input : ℝ) :
    firstStepCost 3 input=input^2+(3+input)^2/2 ∧
    HasDerivAt (firstStepCost 3) (2*input+3+input) input := by
  constructor
  · rw [firstStepCost,actual_final_step_bellman_value]
    rfl
  · convert actual_first_step_derivative 3 input using 1 <;> ring

end SafeLearning.CompleteAppliedFiniteHorizonSourceConsequences
