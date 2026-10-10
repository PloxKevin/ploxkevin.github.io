import SafeLearning.CompleteModulesGramBridge
import SafeLearning.CompleteModulesKernelCorollaries

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesInterpolantPower

open CompleteModulesKernel CompleteModulesGramBridge
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype I] [DecidableEq I]

def queryVector (input : I → X) (x : X) : I → ℝ :=
  fun i => scalarKernel (H:=H) (input i) x

def queryWeights (input : I → X) (x : X) : I → ℝ :=
  (actualGram (H:=H) input)⁻¹ *ᵥ queryVector (H:=H) input x

def powerSquared (input : I → X) (x : X) : ℝ :=
  scalarKernel (H:=H) x x-queryVector (H:=H) input x ⬝ᵥ queryWeights (H:=H) input x

def queryResidual (input : I → X) (x : X) : H :=
  scalarSection (H:=H) x-combination (fun i => scalarSection (H:=H) (input i))
    (queryWeights (H:=H) input x)

theorem actual_query_weights_solve (input : I → X) (x : X)
    (hgram : (actualGram (H:=H) input).PosDef) :
    ∀ i, (∑ j, inner ℝ (scalarSection (H:=H) (input i))
      (scalarSection (H:=H) (input j))*queryWeights (H:=H) input x j)=
      inner ℝ (scalarSection (H:=H) (input i)) (scalarSection (H:=H) x) := by
  have hdet : (CompleteModulesMatrixGP.ridgeMatrix (actualGram (H:=H) input) 0).det≠0 := by
    simpa [CompleteModulesMatrixGP.ridgeMatrix] using hgram.det_pos.ne'
  simpa only [actualGram,CompleteModulesMatrixGP.ridgeMatrix,zero_smul,add_zero,
    zero_mul,queryVector,queryWeights,scalarKernel,featureKernel] using
    inverse_weights_solve_normal_system (fun i => scalarSection (H:=H) (input i)) 0
      hdet (queryVector (H:=H) input x)

theorem power_squared_is_feature_variance (input : I → X) (x : X) :
    powerSquared (H:=H) input x=CompleteModulesKernel.posteriorVariance
      (fun i => scalarSection (H:=H) (input i)) (scalarSection (H:=H) x)
      (queryWeights (H:=H) input x) := by
  unfold powerSquared CompleteModulesKernel.posteriorVariance queryVector scalarKernel featureKernel dotProduct
  rw [real_inner_self_eq_norm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actual_power_is_squared_residual_norm (input : I → X) (x : X)
    (hgram : (actualGram (H:=H) input).PosDef) :
    powerSquared (H:=H) input x=‖queryResidual (H:=H) input x‖^2 := by
  rw [power_squared_is_feature_variance]
  have h := posterior_residual_norm_identity (fun i => scalarSection (H:=H) (input i))
    (scalarSection (H:=H) x) (queryWeights (H:=H) input x) 0
    (by simpa only [zero_mul,add_zero] using actual_query_weights_solve input x hgram)
  simpa only [zero_mul,sub_zero,queryResidual] using h.symm

theorem actual_power_nonnegative (input : I → X) (x : X)
    (hgram : (actualGram (H:=H) input).PosDef) : 0≤powerSquared (H:=H) input x := by
  rw [actual_power_is_squared_residual_norm input x hgram]
  exact sq_nonneg _

theorem inverse_interpolant_is_query_weight_prediction (input : I → X) (labels : I → ℝ)
    (x : X) (hgram : (actualGram (H:=H) input).PosDef) :
    (actualMeanFunction (H:=H) input labels 0) x=∑ i, queryWeights (H:=H) input x i*labels i := by
  rw [actual_mean_is_matrix_posterior]
  have hsym : (fun i => scalarKernel (H:=H) x (input i))=queryVector (H:=H) input x := by
    funext i
    unfold queryVector scalarKernel featureKernel
    exact real_inner_comm _ _
  simp only [CompleteModulesMatrixGP.posteriorMean,CompleteModulesMatrixGP.ridgeMatrix,
    zero_smul,add_zero,hsym]
  have hc := hgram.isHermitian.inv.star_dotProduct_mulVec_comm
    (queryVector (H:=H) input x) labels
  simp only [star_trivial] at hc
  rw [hc]
  simp only [dotProduct,queryWeights,mul_comm]

theorem actual_noise_free_interpolation_error (input : I → X) (function : H) (x : X)
    (hgram : (actualGram (H:=H) input).PosDef) :
    |function x-(actualMeanFunction (H:=H) input (fun i => function (input i)) 0) x|≤
      ‖function‖*Real.sqrt (powerSquared (H:=H) input x) := by
  rw [inverse_interpolant_is_query_weight_prediction input _ x hgram,
    power_squared_is_feature_variance]
  simpa only [scalar_section_reproduces] using noiseless_posterior_error
    (fun i => scalarSection (H:=H) (input i)) (scalarSection (H:=H) x) function
    (queryWeights (H:=H) input x) 0 ‖function‖ (by norm_num) le_rfl
    (by simpa only [zero_mul,add_zero] using actual_query_weights_solve input x hgram)

theorem actual_noise_free_interpolation_bound_sharp (input : I → X) (x : X) (B : ℝ)
    (hB : 0≤B) (hgram : (actualGram (H:=H) input).PosDef)
    (hresidual : queryResidual (H:=H) input x≠0) :
    ∃ function : H, ‖function‖=B ∧ (∀ i, function (input i)=0) ∧
      |function x-(actualMeanFunction (H:=H) input (fun i => function (input i)) 0) x|=
        B*Real.sqrt (powerSquared (H:=H) input x) := by
  let function := CompleteModulesKernelCorollaries.sharpResidualFunction
    (fun i => scalarSection (H:=H) (input i)) (scalarSection (H:=H) x)
    (queryWeights (H:=H) input x) B
  have hs := actual_query_weights_solve input x hgram
  refine ⟨function,CompleteModulesKernelCorollaries.sharp_residual_function_norm
    _ _ _ B hB hresidual,?_,?_⟩
  · simpa only [scalar_section_reproduces] using
      CompleteModulesKernelCorollaries.sharp_residual_function_has_zero_data _ _ _ B hs
  · rw [inverse_interpolant_is_query_weight_prediction input _ x hgram,
      power_squared_is_feature_variance]
    simpa only [scalar_section_reproduces] using
      CompleteModulesKernelCorollaries.sharp_residual_function_attains_error _ _ _ B hB hresidual hs

end SafeLearning.CompleteModulesInterpolantPower
