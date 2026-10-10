import SafeLearning.CompleteModulesLipSDPPracticeOverlap21

set_option autoImplicit false
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesLipSDPPracticeOverlapConsequences21
open CompleteModulesInvalidQC

theorem actual_generic_coupled_increment_constraint_has_the_printed_expansion
    (first second : Fin 2 → ℝ) :
    coupledIncrementQC first second =
      2 * ((first-second) 0-(first-second) 1) *
        ((reluVector first-reluVector second) 0-(reluVector first-reluVector second) 1) -
      2 * ((reluVector first-reluVector second) 0-(reluVector first-reluVector second) 1)^2 := by
  simp [coupledIncrementQC,coupledMultiplier,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

end SafeLearning.CompleteModulesLipSDPPracticeOverlapConsequences21
