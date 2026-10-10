import SafeLearning.CompleteModulesGoSafeODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal
namespace SafeLearning.CompleteModulesGoSafeODERestart
open CompleteModulesGoSafeODE

/-- The given original solution itself supplies a restarted future solution;
Lipschitz uniqueness identifies every alternative with that constructed tail. -/
theorem actual_reached_state_has_a_constructed_unique_future_ode_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E→E) (L : ℝ≥0) (hL : LipschitzWith L field)
    (original : ℝ→E) (time : ℝ) (htime : 0 ≤ time)
    (horiginal : ∀ t,0 ≤ t → HasDerivAt original (field (original t)) t) :
    ∃ restarted : ℝ→E,
      restarted 0=original time ∧
      (∀ t,0 ≤ t → HasDerivAt restarted (field (restarted t)) t) ∧
      (∀ other : ℝ→E,other 0=original time →
        (∀ t,0 ≤ t → HasDerivAt other (field (other t)) t) →
          ∀ t,0 ≤ t → other t=restarted t) ∧
      (∀ t,restarted t=original (time+t)) := by
  refine ⟨fun t=>original (time+t),by simp,?_,?_,fun _=>rfl⟩
  · intro t ht
    exact (horiginal (time+t) (add_nonneg htime ht)).comp_const_add time t
  · intro other hstart hother
    exact actual_autonomous_lipschitz_ode_restart_is_the_original_future_solution
      field L hL original other time htime horiginal hother hstart

end SafeLearning.CompleteModulesGoSafeODERestart
