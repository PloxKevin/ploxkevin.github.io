import SafeLearning.CompleteModulesSandwichHalf
import SafeLearning.CompleteModulesSandwichLMI

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSandwichConsequences
open CompleteModulesSandwich CompleteModulesSandwichHalf CompleteModulesSandwichLMI
  CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesBarrierGradient

variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

theorem actual_negative_definite_matrix_is_not_positive_semidefinite
    [Nonempty K] (matrix : Matrix K K ℝ) (hnegative : (-matrix).PosDef) :
    ¬matrix.PosSemidef := by
  intro hpositive
  let coordinate : K := Classical.choice inferInstance
  have hn : 0 < -(matrix coordinate coordinate) := by simpa using hnegative.diag_pos (i := coordinate)
  have hp : 0 ≤ matrix coordinate coordinate := hpositive.diag_nonneg
  linarith

theorem actual_half_sandwich_multiplier_fails_the_source_lmi
    [Nonempty K] (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (hgram : (outputBlock*outputBlockᵀ-(1/3:ℝ) • (1 : Matrix K K ℝ)).PosDef) :
    ¬(barrierMatrix (actualSandwichOutput outputBlock scale) (actualHalfMultiplier scale) 1
      (actualSandwichInput inputBlock scale)).PosSemidef := by
  rw [actual_unit_gamma_three_block_certificate_iff_lipsdp,actual_unit_gamma_lipsdp_iff_source_schur]
  exact actual_negative_definite_matrix_is_not_positive_semidefinite _
    (actual_half_multiplier_is_negative_when_output_gram_exceeds_one_third
      outputBlock inputBlock hrows scale hscale hgram)

theorem actual_orthogonal_zero_input_half_multiplier_fails_the_source_lmi
    [Nonempty K] (outputBlock : Matrix K O ℝ)
    (hrows : outputBlock*outputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    ¬(barrierMatrix (actualSandwichOutput outputBlock scale) (actualHalfMultiplier scale) 1
      (actualSandwichInput (0 : Matrix K I ℝ) scale)).PosSemidef := by
  rw [actual_unit_gamma_three_block_certificate_iff_lipsdp,actual_unit_gamma_lipsdp_iff_source_schur]
  change ¬(actualHalfSchur outputBlock (0 : Matrix K I ℝ) scale).PosSemidef
  rw [actual_orthogonal_zero_input_half_schur_is_negative_square outputBlock hrows scale hscale]
  intro h
  let coordinate : K := Classical.choice inferInstance
  have hn := h.diag_nonneg (i := coordinate)
  have hp := sq_pos_of_pos (hscale coordinate)
  simp [actualSandwichMultiplier] at hn
  exact (ne_of_gt (hscale coordinate)) hn

/-- The literal source block quadratic retains the QC margin, not only its sign. -/
theorem actual_unit_block_quadratic_is_energy_plus_qc
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (inputIncrement : I → ℝ) (hiddenIncrement : K → ℝ) :
    quadratic (blockCertificate inputWeight outputWeight 0 1 1 multiplier)
      (Sum.elim inputIncrement hiddenIncrement)=
      ‖WithLp.toLp 2 (outputWeight *ᵥ hiddenIncrement)‖^2-
        ‖WithLp.toLp 2 inputIncrement‖^2+
        2*(hiddenIncrement ⬝ᵥ (Matrix.diagonal multiplier *ᵥ
          (inputWeight *ᵥ inputIncrement-hiddenIncrement))) := by
  rw [← canonical_certificate_is_stated_block_matrix]
  unfold canonicalCertificate
  rw [certificate_quadratic_identity]
  simp only [Matrix.fromCols_mulVec_sumElim,Matrix.zero_mulVec,Matrix.one_mulVec,
    add_zero,zero_add,squared_norm_of_coordinates,zero_mul,one_mul,zero_add,
    Matrix.mulVec_diagonal,dotProduct,Pi.sub_apply]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate hcoordinate
  ring

/-- Arbitrary biases cancel in the genuine activation increment. -/
theorem actual_unit_slope_activation_incremental_qc
    (inputWeight : Matrix K I ℝ) (bias : K → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1)
    (multiplier : K → ℝ) (hmultiplier : ∀ coordinate,0 ≤ multiplier coordinate)
    (first second : I → ℝ) :
    0 ≤ 2*((hiddenValues inputWeight bias activation first-hiddenValues inputWeight bias activation second) ⬝ᵥ
      (Matrix.diagonal multiplier *ᵥ (inputWeight *ᵥ (first-second)-
        (hiddenValues inputWeight bias activation first-hiddenValues inputWeight bias activation second)))) := by
  simp only [dotProduct,Matrix.mulVec_diagonal,Pi.sub_apply,Finset.mul_sum]
  apply Finset.sum_nonneg
  intro coordinate hcoordinate
  have h := scalar_slope_quadratic_constraint activation 0 1 hactivation
    ((inputWeight *ᵥ first) coordinate+bias coordinate)
    ((inputWeight *ᵥ second) coordinate+bias coordinate)
  have hw := mul_nonneg (hmultiplier coordinate) h
  simp only [hiddenValues,Matrix.mulVec_sub,Pi.sub_apply] at *
  nlinarith

theorem actual_unit_network_source_energy_margin
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1)
    (multiplier : K → ℝ) (hmultiplier : ∀ coordinate,0 ≤ multiplier coordinate)
    (hcertificate : (-(blockCertificate inputWeight outputWeight 0 1 1 multiplier)).PosSemidef)
    (first second : I → ℝ) :
    2*((hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second) ⬝ᵥ
      (Matrix.diagonal multiplier *ᵥ (inputWeight *ᵥ (first-second)-
        (hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second)))) ≤
      ‖WithLp.toLp 2 (first-second)‖^2-
      ‖WithLp.toLp 2 (oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation first-
        oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation second)‖^2 ∧
    0 ≤ 2*((hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second) ⬝ᵥ
      (Matrix.diagonal multiplier *ᵥ (inputWeight *ᵥ (first-second)-
        (hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second)))) := by
  have h := negative_semidefinite_quadratic _ hcertificate
    (Sum.elim (first-second) (hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second))
  rw [actual_unit_block_quadratic_is_energy_plus_qc] at h
  have ho : outputWeight *ᵥ (hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second)=
      oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation first-
        oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation second := by
    simp [oneHiddenNetwork,Matrix.mulVec_sub]
  rw [ho] at h
  exact ⟨by linarith,actual_unit_slope_activation_incremental_qc inputWeight firstBias activation
    hactivation multiplier hmultiplier first second⟩

theorem actual_sandwich_layer_has_literal_source_qc_energy_margin
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (hactivation : slopeRestricted activation 0 1) (first second : I → ℝ) :
    let inputWeight := actualSandwichInput inputBlock scale
    let outputWeight := actualSandwichOutput outputBlock scale
    let hiddenIncrement := hiddenValues inputWeight firstBias activation first-hiddenValues inputWeight firstBias activation second
    2*(hiddenIncrement ⬝ᵥ (Matrix.diagonal (actualSandwichMultiplier scale) *ᵥ
        (inputWeight *ᵥ (first-second)-hiddenIncrement))) ≤
      ‖WithLp.toLp 2 (first-second)‖^2-
      ‖WithLp.toLp 2 (oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation first-
        oneHiddenNetwork inputWeight outputWeight firstBias lastBias activation second)‖^2 ∧
    0 ≤ 2*(hiddenIncrement ⬝ᵥ (Matrix.diagonal (actualSandwichMultiplier scale) *ᵥ
        (inputWeight *ᵥ (first-second)-hiddenIncrement))) := by
  have hp := actual_sandwich_three_block_matrix_is_positive_semidefinite outputBlock inputBlock hrows scale hscale
  rw [actual_unit_gamma_three_block_certificate_iff_lipsdp] at hp
  exact actual_unit_network_source_energy_margin _ _ firstBias lastBias activation hactivation
    (actualSandwichMultiplier scale) (fun coordinate => sq_nonneg (scale coordinate)) hp first second

end SafeLearning.CompleteModulesSandwichConsequences
