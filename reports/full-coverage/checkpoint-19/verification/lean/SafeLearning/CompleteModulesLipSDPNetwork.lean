import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesLipSDPNetwork

open CompleteModulesLipSDP
variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K]

def hiddenValues (weight : Matrix K I ℝ) (bias : K → ℝ)
    (activation : ℝ → ℝ) (input : I → ℝ) : K → ℝ :=
  fun k => activation ((weight *ᵥ input) k+bias k)

def oneHiddenNetwork (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ) (input : I → ℝ) : O → ℝ :=
  lastWeight *ᵥ hiddenValues firstWeight firstBias activation input+lastBias

def liftedState (weight : Matrix K I ℝ) (bias : K → ℝ)
    (activation : ℝ → ℝ) (input : I → ℝ) : I ⊕ K → ℝ :=
  Sum.elim input (hiddenValues weight bias activation input)

def canonicalCertificate (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ) : Matrix (I ⊕ K) (I ⊕ K) ℝ :=
  certificateMatrix (Matrix.fromCols firstWeight (0 : Matrix K K ℝ))
    (Matrix.fromCols (0 : Matrix K I ℝ) (1 : Matrix K K ℝ))
    (Matrix.fromCols (1 : Matrix I I ℝ) (0 : Matrix I K ℝ))
    (Matrix.fromCols (0 : Matrix O I ℝ) lastWeight) alpha beta rho multiplier

def blockCertificate (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ) : Matrix (I ⊕ K) (I ⊕ K) ℝ :=
  Matrix.fromBlocks
    ((-2*alpha*beta) • (firstWeightᵀ*Matrix.diagonal multiplier*firstWeight)-rho • 1)
    ((alpha+beta) • (firstWeightᵀ*Matrix.diagonal multiplier))
    ((alpha+beta) • (Matrix.diagonal multiplier*firstWeight))
    ((-2:ℝ) • Matrix.diagonal multiplier+lastWeightᵀ*lastWeight)

theorem canonical_certificate_is_stated_block_matrix (firstWeight : Matrix K I ℝ)
    (lastWeight : Matrix O K ℝ) (alpha beta rho : ℝ) (multiplier : K → ℝ) :
    canonicalCertificate firstWeight lastWeight alpha beta rho multiplier=
      blockCertificate firstWeight lastWeight alpha beta rho multiplier := by
  unfold canonicalCertificate certificateMatrix blockCertificate
  simp only [Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.fromRows_mul_fromCols,
    Matrix.transpose_zero,Matrix.transpose_one,Matrix.zero_mul,Matrix.mul_zero,
    Matrix.mul_one,Matrix.one_mul]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring

theorem actual_network_lipsdp_soundness (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ)
    (hactivation : slopeRestricted activation alpha beta)
    (hmultiplier : ∀ k, 0 ≤ multiplier k) (hrho : 0 ≤ rho)
    (hcertificate : (-(canonicalCertificate firstWeight lastWeight alpha beta rho multiplier)).PosSemidef)
    (first second : I → ℝ) :
    ‖WithLp.toLp 2 (oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation first-
      oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation second)‖ ≤
      Real.sqrt rho*‖WithLp.toLp 2 (first-second)‖ := by
  have hpre : ∀ input : I → ℝ, Matrix.fromCols firstWeight (0 : Matrix K K ℝ) *ᵥ
      liftedState firstWeight firstBias activation input=firstWeight *ᵥ input := by
    intro input
    simp [liftedState,Matrix.fromCols_mulVec_sumElim]
  have hhidden : Matrix.fromCols (0 : Matrix K I ℝ) (1 : Matrix K K ℝ) *ᵥ
      (liftedState firstWeight firstBias activation first-
        liftedState firstWeight firstBias activation second)=
      hiddenValues firstWeight firstBias activation first-hiddenValues firstWeight firstBias activation second := by
    simp [Matrix.mulVec_sub,liftedState,Matrix.fromCols_mulVec_sumElim]
  have hinput : Matrix.fromCols (1 : Matrix I I ℝ) (0 : Matrix I K ℝ) *ᵥ
      (liftedState firstWeight firstBias activation first-
        liftedState firstWeight firstBias activation second)=first-second := by
    simp [Matrix.mulVec_sub,liftedState,Matrix.fromCols_mulVec_sumElim]
  have houtput : Matrix.fromCols (0 : Matrix O I ℝ) lastWeight *ᵥ
      (liftedState firstWeight firstBias activation first-
        liftedState firstWeight firstBias activation second)=
      oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation first-
        oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation second := by
    simp [Matrix.mulVec_sub,liftedState,Matrix.fromCols_mulVec_sumElim,oneHiddenNetwork]
  have h := finite_lifted_lipsdp_soundness
    (Matrix.fromCols firstWeight (0 : Matrix K K ℝ))
    (Matrix.fromCols (0 : Matrix K I ℝ) (1 : Matrix K K ℝ))
    (Matrix.fromCols (1 : Matrix I I ℝ) (0 : Matrix I K ℝ))
    (Matrix.fromCols (0 : Matrix O I ℝ) lastWeight)
    activation alpha beta rho multiplier hactivation hmultiplier hrho hcertificate
    (liftedState firstWeight firstBias activation first)
    (liftedState firstWeight firstBias activation second) firstBias (by
      intro k
      rw [hhidden,hpre,hpre]
      rfl)
  rwa [hinput,houtput] at h

theorem actual_block_matrix_certificate_bounds_network
    (firstWeight : Matrix K I ℝ) (lastWeight : Matrix O K ℝ)
    (firstBias : K → ℝ) (lastBias : O → ℝ) (activation : ℝ → ℝ)
    (alpha beta rho : ℝ) (multiplier : K → ℝ)
    (hactivation : slopeRestricted activation alpha beta)
    (hmultiplier : ∀ k, 0 ≤ multiplier k) (hrho : 0 ≤ rho)
    (hcertificate : (-(blockCertificate firstWeight lastWeight alpha beta rho multiplier)).PosSemidef)
    (first second : I → ℝ) :
    ‖WithLp.toLp 2 (oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation first-
      oneHiddenNetwork firstWeight lastWeight firstBias lastBias activation second)‖ ≤
      Real.sqrt rho*‖WithLp.toLp 2 (first-second)‖ :=
  actual_network_lipsdp_soundness firstWeight lastWeight firstBias lastBias activation
    alpha beta rho multiplier hactivation hmultiplier hrho
    (by rwa [canonical_certificate_is_stated_block_matrix]) first second

end SafeLearning.CompleteModulesLipSDPNetwork
