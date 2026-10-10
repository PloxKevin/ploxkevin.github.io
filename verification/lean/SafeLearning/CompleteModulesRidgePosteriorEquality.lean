import SafeLearning.CompleteModulesGramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesRidgePosteriorEquality
open CompleteModulesKernel CompleteModulesGramBridge
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

def literalRidgeObjective (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (function : H) : ℝ :=
  (∑ i,(labels i-function (input i))^2)+regularizer*‖function‖^2

theorem actual_objective_has_the_literal_source_residual_convention
    (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (function : H) :
    literalRidgeObjective input labels regularizer function =
      actualRidgeObjective input labels regularizer function := by
  unfold literalRidgeObjective actualRidgeObjective
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actual_global_ridge_minimizer_iff_the_actual_inverse_kernel_function
    (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (hpos : 0<regularizer) (function : H) :
    (∀ competitor : H,literalRidgeObjective input labels regularizer function ≤
      literalRidgeObjective input labels regularizer competitor) ↔
    function =actualMeanFunction (H:=H) input labels regularizer := by
  simp only [actual_objective_has_the_literal_source_residual_convention]
  constructor
  · intro hf
    obtain ⟨minimizer,hm,hunique⟩ := actual_rkhs_ridge_minimizer_exists_unique
      (H:=H) input labels regularizer hpos
    exact (hunique function hf).trans
      (hunique (actualMeanFunction (H:=H) input labels regularizer)
        (actual_inverse_mean_globally_minimizes_ridge input labels regularizer hpos)).symm
  · rintro rfl
    exact actual_inverse_mean_globally_minimizes_ridge input labels regularizer hpos

theorem actual_every_global_ridge_minimizer_has_the_source_posterior_mean_formula
    (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (hpos : 0<regularizer)
    (function : H)
    (hmin : ∀ competitor : H,literalRidgeObjective input labels regularizer function ≤
      literalRidgeObjective input labels regularizer competitor) (x : X) :
    function x=CompleteModulesMatrixGP.posteriorMean (actualGram (H:=H) input)
      (fun i=>scalarKernel (H:=H) x (input i)) labels regularizer := by
  rw [(actual_global_ridge_minimizer_iff_the_actual_inverse_kernel_function
    input labels regularizer hpos function).mp hmin]
  exact actual_mean_is_matrix_posterior input labels regularizer x

theorem actual_unique_source_ridge_function_equals_the_posterior_formula
    (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (hpos : 0<regularizer) :
    ∃! function : H,
      (∀ competitor : H,literalRidgeObjective input labels regularizer function ≤
        literalRidgeObjective input labels regularizer competitor) ∧
      (∀ x : X,function x=CompleteModulesMatrixGP.posteriorMean (actualGram (H:=H) input)
        (fun i=>scalarKernel (H:=H) x (input i)) labels regularizer) := by
  refine ⟨actualMeanFunction (H:=H) input labels regularizer,⟨?_,?_⟩,?_⟩
  · exact (actual_global_ridge_minimizer_iff_the_actual_inverse_kernel_function
      input labels regularizer hpos _).mpr rfl
  · exact actual_mean_is_matrix_posterior input labels regularizer
  · intro function hfunction
    exact (actual_global_ridge_minimizer_iff_the_actual_inverse_kernel_function
      input labels regularizer hpos function).mp hfunction.1

end SafeLearning.CompleteModulesRidgePosteriorEquality
