import SafeLearning.CompleteModulesBarrierGradient
import SafeLearning.CompleteModulesLipSDPNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesBarrierSoundness

open CompleteModulesBarrierGradient CompleteModulesLipSDP CompleteModulesLipSDPNetwork
variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

def leadingBarrierBlock (firstWeight : Matrix K I ℝ) (multiplier : K → ℝ)
    (gain : ℝ) : Matrix (I ⊕ K) (I ⊕ K) ℝ :=
  Matrix.fromBlocks (gain^2 • 1) (-(firstWeightᵀ*Matrix.diagonal multiplier))
    (-(Matrix.diagonal multiplier*firstWeight)) ((2:ℝ) • Matrix.diagonal multiplier)

def outputBarrierCross (lastWeight : Matrix O K ℝ) : Matrix (I ⊕ K) O ℝ :=
  Matrix.fromRows (0 : Matrix I O ℝ) (-lastWeightᵀ)

theorem actual_barrier_reassociates_to_output_schur_block
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) :
    (barrierMatrix lastWeight multiplier gain firstWeight).submatrix
      (Equiv.sumAssoc I K O) (Equiv.sumAssoc I K O)=
      Matrix.fromBlocks (leadingBarrierBlock firstWeight multiplier gain)
        (outputBarrierCross (I := I) lastWeight) (outputBarrierCross (I := I) lastWeight)ᴴ
        (1 : Matrix O O ℝ) := by
  ext i j
  rcases i with (i|i) | i <;> rcases j with (j|j) | j <;>
    simp [barrierMatrix,leadingBarrierBlock,outputBarrierCross,Matrix.submatrix_apply,
      Equiv.sumAssoc,Matrix.conjTranspose_apply]

theorem actual_barrier_schur_complement_is_negative_lipsdp_certificate
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) :
    leadingBarrierBlock firstWeight multiplier gain-
      outputBarrierCross (I := I) lastWeight*(1 : Matrix O O ℝ)⁻¹*
        (outputBarrierCross (I := I) lastWeight)ᴴ=
      -(blockCertificate firstWeight lastWeight 0 1 (gain^2) multiplier) := by
  have hinverse : (1 : Matrix O O ℝ)⁻¹=1 := by simp [Matrix.inv_def]
  rw [hinverse,Matrix.mul_one]
  unfold leadingBarrierBlock outputBarrierCross blockCertificate
  simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromRows_mul_fromCols,
    Matrix.conjTranspose_zero,Matrix.conjTranspose_neg,Matrix.conjTranspose_conjTranspose,
    Matrix.zero_mul,Matrix.mul_zero,neg_mul_neg,mul_zero,zero_mul,zero_smul,
    zero_sub,zero_add,one_smul]
  ext i j
  cases i <;> cases j <;> simp <;> ring

theorem actual_positive_barrier_implies_lipsdp_feasibility
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ)
    (hpositive : (barrierMatrix lastWeight multiplier gain firstWeight).PosDef) :
    (-(blockCertificate firstWeight lastWeight 0 1 (gain^2) multiplier)).PosSemidef := by
  letI : Invertible (1 : Matrix O O ℝ) := invertibleOne
  have hblock := (hpositive.submatrix (Equiv.sumAssoc I K O).injective).posSemidef
  rw [actual_barrier_reassociates_to_output_schur_block] at hblock
  have hschur := (Matrix.PosDef.fromBlocks₂₂ (leadingBarrierBlock firstWeight multiplier gain)
    (outputBarrierCross (I := I) lastWeight) (Matrix.PosDef.one : (1 : Matrix O O ℝ).PosDef)).mp hblock
  rwa [actual_barrier_schur_complement_is_negative_lipsdp_certificate] at hschur

theorem actual_positive_barrier_has_positive_diagonal_multiplier
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ)
    (hpositive : (barrierMatrix lastWeight multiplier gain firstWeight).PosDef) :
    ∀ k, 0 < multiplier k := by
  intro k
  have h := hpositive.diag_pos (i := Sum.inr (Sum.inl k))
  simp [barrierMatrix,Matrix.diagonal_apply] at h
  linarith

theorem actual_accepted_positive_barrier_certifies_actual_network
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (hgain : 0 ≤ gain)
    (hactivation : slopeRestricted activation 0 1)
    (hpositive : (barrierMatrix lastWeight multiplier gain firstWeight).PosDef)
    (first second : I → ℝ) :
    ‖WithLp.toLp 2 (oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation first-
      oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation second)‖ ≤
        gain*‖WithLp.toLp 2 (first-second)‖ := by
  have h := actual_block_matrix_certificate_bounds_network firstWeight lastWeight firstBias lastBias
    activation 0 1 (gain^2) multiplier hactivation
    (fun k => (actual_positive_barrier_has_positive_diagonal_multiplier firstWeight lastWeight
      multiplier gain hpositive k).le) (sq_nonneg gain)
    (actual_positive_barrier_implies_lipsdp_feasibility firstWeight lastWeight multiplier gain hpositive)
    first second
  simpa only [Real.sqrt_sq hgain] using h

end SafeLearning.CompleteModulesBarrierSoundness
