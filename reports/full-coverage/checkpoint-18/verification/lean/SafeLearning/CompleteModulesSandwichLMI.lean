import SafeLearning.CompleteModulesSandwich

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSandwichLMI
open CompleteModulesSandwich CompleteModulesLipSDP CompleteModulesLipSDPNetwork
  CompleteModulesBarrierGradient CompleteModulesBarrierSoundness

variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

theorem actual_unit_gamma_three_block_certificate_iff_lipsdp
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ) (multiplier : K → ℝ) :
    (barrierMatrix outputWeight multiplier 1 inputWeight).PosSemidef ↔
      (-(blockCertificate inputWeight outputWeight 0 1 1 multiplier)).PosSemidef := by
  letI : Invertible (1 : Matrix O O ℝ) := invertibleOne
  rw [← Matrix.posSemidef_submatrix_equiv (Equiv.sumAssoc I K O),
    actual_barrier_reassociates_to_output_schur_block,
    Matrix.PosDef.fromBlocks₂₂ _ _ (Matrix.PosDef.one : (1 : Matrix O O ℝ).PosDef),
    actual_barrier_schur_complement_is_negative_lipsdp_certificate]
  norm_num

theorem actual_unit_gamma_lipsdp_iff_source_schur
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ) (multiplier : K → ℝ) :
    (-(blockCertificate inputWeight outputWeight 0 1 1 multiplier)).PosSemidef ↔
      ((2:ℝ) • Matrix.diagonal multiplier-outputWeightᵀ*outputWeight-
        Matrix.diagonal multiplier*inputWeight*inputWeightᵀ*Matrix.diagonal multiplier).PosSemidef := by
  letI : Invertible (1 : Matrix I I ℝ) := invertibleOne
  have he : -(blockCertificate inputWeight outputWeight 0 1 1 multiplier)=
      Matrix.fromBlocks (1 : Matrix I I ℝ) (-(inputWeightᵀ*Matrix.diagonal multiplier))
        (-(inputWeightᵀ*Matrix.diagonal multiplier))ᴴ
        ((2:ℝ) • Matrix.diagonal multiplier-outputWeightᵀ*outputWeight) := by
    have hb : (-(inputWeightᵀ*Matrix.diagonal multiplier))ᴴ=-(Matrix.diagonal multiplier*inputWeight) := by
      change (-(inputWeightᵀ*Matrix.diagonal multiplier))ᵀ=_
      simp [Matrix.transpose_mul]
    rw [hb]
    ext row column
    cases row <;> cases column <;> simp [blockCertificate] <;> ring
  rw [he,Matrix.PosDef.fromBlocks₁₁ _ _ (Matrix.PosDef.one : (1 : Matrix I I ℝ).PosDef)]
  have hb : (-(inputWeightᵀ*Matrix.diagonal multiplier))ᴴ=-(Matrix.diagonal multiplier*inputWeight) := by
    change (-(inputWeightᵀ*Matrix.diagonal multiplier))ᵀ=_
    simp [Matrix.transpose_mul]
  simp only [hb,show (1 : Matrix I I ℝ)⁻¹=1 by simp [Matrix.inv_def],
    Matrix.mul_one,Matrix.neg_mul,Matrix.mul_neg,neg_neg,Matrix.mul_assoc]

theorem actual_sandwich_three_block_matrix_is_positive_semidefinite
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    (barrierMatrix (actualSandwichOutput outputBlock scale) (actualSandwichMultiplier scale) 1
      (actualSandwichInput inputBlock scale)).PosSemidef := by
  rw [actual_unit_gamma_three_block_certificate_iff_lipsdp,actual_unit_gamma_lipsdp_iff_source_schur,
    actual_sandwich_source_schur_expression_is_zero outputBlock inputBlock hrows scale hscale]
  exact Matrix.PosSemidef.zero

theorem actual_sandwich_layer_is_euclidean_nonexpansive
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1) (first second : I → ℝ) :
    ‖WithLp.toLp 2 (oneHiddenNetwork (actualSandwichInput inputBlock scale)
        (actualSandwichOutput outputBlock scale) firstBias lastBias activation first-
      oneHiddenNetwork (actualSandwichInput inputBlock scale) (actualSandwichOutput outputBlock scale)
        firstBias lastBias activation second)‖ ≤ ‖WithLp.toLp 2 (first-second)‖ := by
  have hp := actual_sandwich_three_block_matrix_is_positive_semidefinite outputBlock inputBlock hrows scale hscale
  rw [actual_unit_gamma_three_block_certificate_iff_lipsdp] at hp
  have h := actual_block_matrix_certificate_bounds_network
    (actualSandwichInput inputBlock scale) (actualSandwichOutput outputBlock scale)
    firstBias lastBias activation 0 1 1 (actualSandwichMultiplier scale) hactivation
    (fun coordinate => sq_nonneg (scale coordinate)) (by norm_num) hp first second
  simpa using h

end SafeLearning.CompleteModulesSandwichLMI
