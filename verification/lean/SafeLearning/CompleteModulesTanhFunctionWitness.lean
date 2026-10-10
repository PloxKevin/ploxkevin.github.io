import SafeLearning.CompleteModulesTanhFTCRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesTanhFunctionWitness
open CompleteModulesTanhRefinement CompleteModulesTanhFTCRefinement
open CompleteModulesDiagonalQC CompleteModulesLipSDP

def actualSectorFunctions (lower : ℝ) : Set (ℝ → ℝ) :=
  {activation | ∀ input : ℝ, 0 ≤ quadratic (actualSectorQCMatrix lower 1) ![input,activation input]}

theorem actual_linear_activation_satisfies_the_weaker_qc_for_every_input (lower input : ℝ) :
    quadratic (actualSectorQCMatrix lower 1) ![input,lower*input] = 0 := by
  rw [actual_sector_qc_matrix_has_the_literal_quadratic]
  dsimp [scalarQC]
  ring

theorem actual_larger_lower_sector_excludes_a_genuine_weaker_sector_function
    (small large : ℝ) (hs : 0 ≤ small) (hgap : small < large) (hu : large ≤ 1) :
    actualSectorFunctions large ⊆ actualSectorFunctions small ∧
      (fun input : ℝ => small*input) ∈ actualSectorFunctions small ∧
      (fun input : ℝ => small*input) ∉ actualSectorFunctions large := by
  have h := actual_strictly_larger_lower_slope_strictly_shrinks_the_qc_abstraction small large hs hgap hu
  refine ⟨?_,?_,?_⟩
  · intro activation ha input
    rw [actual_sector_qc_matrix_has_the_literal_quadratic]
    have hp : (input,activation input) ∈ actualAllowedQCPairs large := by
      have hp := ha input
      rwa [actual_sector_qc_matrix_has_the_literal_quadratic] at hp
    exact h.1 hp
  · intro input
    rw [actual_linear_activation_satisfies_the_weaker_qc_for_every_input]
  · intro ha
    apply h.2.2
    have hp := ha 1
    change 0 ≤ scalarQC large 1 1 small
    simpa only [actual_sector_qc_matrix_has_the_literal_quadratic,mul_one] using hp

end SafeLearning.CompleteModulesTanhFunctionWitness
