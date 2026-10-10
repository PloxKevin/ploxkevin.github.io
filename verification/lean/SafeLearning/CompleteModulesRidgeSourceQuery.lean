import SafeLearning.CompleteModulesRidgePosteriorEquality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesRidgeSourceQuery
open CompleteModulesKernel CompleteModulesGramBridge CompleteModulesRidgePosteriorEquality
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

theorem actual_source_kernel_query_orientation (input : I→X) (x : X) :
    (fun i=>scalarKernel (H:=H) x (input i))=
      (fun i=>scalarKernel (H:=H) (input i) x) := by
  funext i
  exact real_inner_comm _ _

theorem actual_source_gram_entries_are_the_actual_rkhs_kernel (input : I→X) (i j : I) :
    actualGram (H:=H) input i j=(RKHS.kernel H (input i) (input j)) 1 := by
  exact scalar_kernel_is_actual_kernel (input i) (input j)

theorem actual_every_minimizer_equals_the_literal_data_query_posterior
    (input : I→X) (labels : I→ℝ) (regularizer : ℝ) (hpos : 0<regularizer)
    (function : H)
    (hmin : ∀ competitor : H,literalRidgeObjective input labels regularizer function ≤
      literalRidgeObjective input labels regularizer competitor) (x : X) :
    function x=CompleteModulesMatrixGP.posteriorMean (actualGram (H:=H) input)
      (fun i=>scalarKernel (H:=H) (input i) x) labels regularizer := by
  rw [←actual_source_kernel_query_orientation input x]
  exact actual_every_global_ridge_minimizer_has_the_source_posterior_mean_formula
    input labels regularizer hpos function hmin x

end SafeLearning.CompleteModulesRidgeSourceQuery
