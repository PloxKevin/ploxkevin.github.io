import SafeLearning.CompleteAppliedIntegratorEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace SafeLearning.CompleteAppliedIntegratorGramian
open CompleteAppliedIntegratorEnergy

def sourceGramian : ℝ :=
  ∫t in (0:ℝ)..2,Real.exp (0*t)*(1:ℝ)*1*Real.exp (0*t)
def optimalState (t : ℝ) : ℝ := t/2
def optimalInput (_t : ℝ) : ℝ := 1/2

theorem actual_scalar_integrator_gramian_and_inverse_energy :
    sourceGramian=2 ∧ (1:ℝ)^2/sourceGramian=1/2 := by
  norm_num [sourceGramian]

theorem actual_optimal_control_is_an_existing_absolutely_continuous_integrator_trajectory :
    AbsolutelyContinuousOnInterval optimalState 0 2 ∧ optimalState 0=0 ∧
    optimalState 2=1 ∧ (∀t : ℝ,HasDerivAt optimalState (optimalInput t) t) := by
  refine ⟨?_,by norm_num [optimalState],by norm_num [optimalState],?_⟩
  · apply ContDiffOn.absolutelyContinuousOnInterval
    unfold optimalState
    fun_prop
  · intro t
    unfold optimalState optimalInput
    convert (hasDerivAt_id t).div_const 2 using 1 <;> simp

theorem actual_source_optimal_input_attains_the_true_least_energy :
    MemLp optimalInput 2 window ∧
    (∫t,optimalInput t ∂window)=1 ∧
    (∫t,optimalInput t^2 ∂window)=1/2 ∧ IsLeast admissibleEnergies (1/2:ℝ) := by
  have h := actual_constant_input_reaches_one_and_has_half_energy
  exact ⟨h.1,h.2.1,h.2.2.1,actual_horizon_two_gramian_and_true_minimum_energy.2.1⟩

end SafeLearning.CompleteAppliedIntegratorGramian
