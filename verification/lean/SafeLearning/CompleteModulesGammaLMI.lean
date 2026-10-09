import SafeLearning.CompleteModulesBarrierSoundness

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGammaLMI
open CompleteModulesLipSDPNetwork CompleteModulesBarrierSoundness

variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

def actualGammaLeading (inputWeight : Matrix K I ℝ) (multiplier : K → ℝ) (gain : ℝ) :
    Matrix (I ⊕ K) (I ⊕ K) ℝ :=
  Matrix.fromBlocks (gain • (1 : Matrix I I ℝ)) (-(inputWeightᵀ*Matrix.diagonal multiplier))
    (-(Matrix.diagonal multiplier*inputWeight)) ((2:ℝ) • Matrix.diagonal multiplier)

def actualGammaCertificate (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ :=
  Matrix.fromBlocks (gain • (1 : Matrix I I ℝ))
    (Matrix.fromCols (-(inputWeightᵀ*Matrix.diagonal multiplier)) (0 : Matrix I O ℝ))
    (Matrix.fromRows (-(Matrix.diagonal multiplier*inputWeight)) (0 : Matrix O I ℝ))
    (Matrix.fromBlocks ((2:ℝ) • Matrix.diagonal multiplier) (-outputWeightᵀ)
      (-outputWeight) (gain • (1 : Matrix O O ℝ)))

theorem actual_positive_scalar_identity_inverse (gain : ℝ) (hgain : 0 < gain) :
    (gain • (1 : Matrix O O ℝ))⁻¹=(1/gain:ℝ) • (1 : Matrix O O ℝ) := by
  apply Matrix.inv_eq_right_inv
  simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hgain.ne']

theorem actual_gamma_matrix_output_reassociation
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ) (multiplier : K → ℝ) (gain : ℝ) :
    (actualGammaCertificate inputWeight outputWeight multiplier gain).submatrix
      (Equiv.sumAssoc I K O) (Equiv.sumAssoc I K O)=
    Matrix.fromBlocks (actualGammaLeading inputWeight multiplier gain)
      (outputBarrierCross (I := I) outputWeight) (outputBarrierCross (I := I) outputWeight)ᴴ
        (gain • (1 : Matrix O O ℝ)) := by
  ext row column
  rcases row with (row|row)|row <;> rcases column with (column|column)|column <;>
    simp [actualGammaCertificate,actualGammaLeading,outputBarrierCross,Matrix.submatrix_apply,
      Equiv.sumAssoc,Matrix.conjTranspose_apply]

theorem actual_positive_scalar_preserves_positive_semidefinite
    {N : Type*} [Fintype N] [DecidableEq N] (matrix : Matrix N N ℝ)
    (gain : ℝ) (hgain : 0 < gain) :
    (gain • matrix).PosSemidef ↔ matrix.PosSemidef := by
  constructor
  · intro h
    have hs := h.smul (show (0:ℝ) ≤ 1/gain by positivity)
    simpa [smul_smul,hgain.ne'] using hs
  · intro h
    exact h.smul hgain.le

theorem actual_gamma_output_schur_is_literal_source_block
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (hgain : 0 < gain) :
    actualGammaLeading inputWeight multiplier gain-
      outputBarrierCross (I := I) outputWeight*(gain • (1 : Matrix O O ℝ))⁻¹*
        (outputBarrierCross (I := I) outputWeight)ᴴ=
    Matrix.fromBlocks (gain • (1 : Matrix I I ℝ))
      (-(inputWeightᵀ*Matrix.diagonal multiplier)) (-(Matrix.diagonal multiplier*inputWeight))
      ((2:ℝ) • Matrix.diagonal multiplier-(1/gain:ℝ) • (outputWeightᵀ*outputWeight)) := by
  rw [actual_positive_scalar_identity_inverse gain hgain]
  unfold actualGammaLeading outputBarrierCross
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromRows_mul_fromCols,
    Matrix.conjTranspose_zero,Matrix.conjTranspose_neg,Matrix.conjTranspose_conjTranspose,
    Matrix.zero_mul,Matrix.mul_zero,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
  ext row column
  cases row <;> cases column <;> simp <;> ring

theorem actual_gamma_scaled_schur_is_negative_lipsdp
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (hgain : 0 < gain) :
    gain • (Matrix.fromBlocks (gain • (1 : Matrix I I ℝ))
      (-(inputWeightᵀ*Matrix.diagonal multiplier)) (-(Matrix.diagonal multiplier*inputWeight))
      ((2:ℝ) • Matrix.diagonal multiplier-(1/gain:ℝ) • (outputWeightᵀ*outputWeight)))=
      -(blockCertificate inputWeight outputWeight 0 1 (gain^2) (gain • multiplier)) := by
  ext row column
  cases row <;> cases column <;>
    simp [blockCertificate,Matrix.diagonal_smul,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.smul_apply,smul_smul] <;> field_simp [hgain.ne'] <;> ring

theorem actual_gamma_lmi_iff_source_lipsdp
    (inputWeight : Matrix K I ℝ) (outputWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (hgain : 0 < gain) :
    (actualGammaCertificate inputWeight outputWeight multiplier gain).PosSemidef ↔
      (-(blockCertificate inputWeight outputWeight 0 1 (gain^2) (gain • multiplier))).PosSemidef := by
  have hd : (gain • (1 : Matrix O O ℝ)).PosDef := Matrix.PosDef.one.smul hgain
  letI := hd.isUnit.invertible
  rw [← Matrix.posSemidef_submatrix_equiv (Equiv.sumAssoc I K O),actual_gamma_matrix_output_reassociation,
    Matrix.PosDef.fromBlocks₂₂ _ _ hd,actual_gamma_output_schur_is_literal_source_block inputWeight outputWeight multiplier gain hgain,
    ← actual_positive_scalar_preserves_positive_semidefinite _ gain hgain,
    actual_gamma_scaled_schur_is_negative_lipsdp inputWeight outputWeight multiplier gain hgain]

theorem actual_source_squared_gain_has_same_positive_bound (gain : ℝ) (hgain : 0 < gain) :
    Real.sqrt (gain^2)=gain := Real.sqrt_sq hgain.le

end SafeLearning.CompleteModulesGammaLMI
