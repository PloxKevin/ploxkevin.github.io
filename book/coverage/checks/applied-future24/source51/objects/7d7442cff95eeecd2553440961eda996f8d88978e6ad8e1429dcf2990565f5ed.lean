import SafeLearning.CompleteModulesLogDet

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace SafeLearning.CompleteModulesBarrierGradient

open CompleteModulesLogDet
variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

def barrierMatrix (lastWeight : Matrix O K ℝ) (multiplier : K → ℝ)
    (gain : ℝ) (firstWeight : Matrix K I ℝ) : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ :=
  Matrix.fromBlocks (gain^2 • (1 : Matrix I I ℝ))
    (Matrix.fromCols (-(firstWeightᵀ*Matrix.diagonal multiplier)) (0 : Matrix I O ℝ))
    (Matrix.fromRows (-(Matrix.diagonal multiplier*firstWeight)) (0 : Matrix O I ℝ))
    (Matrix.fromBlocks ((2:ℝ) • Matrix.diagonal multiplier) (-lastWeightᵀ)
      (-lastWeight) (1 : Matrix O O ℝ))

def barrierVariation (multiplier : K → ℝ) (perturbation : Matrix K I ℝ) :
    Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ :=
  Matrix.fromBlocks (0 : Matrix I I ℝ)
    (Matrix.fromCols (-(perturbationᵀ*Matrix.diagonal multiplier)) (0 : Matrix I O ℝ))
    (Matrix.fromRows (-(Matrix.diagonal multiplier*perturbation)) (0 : Matrix O I ℝ))
    (0 : Matrix (K ⊕ O) (K ⊕ O) ℝ)

def variationLinear (multiplier : K → ℝ) : Matrix K I ℝ →ₗ[ℝ]
    Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ where
  toFun := barrierVariation multiplier
  map_add' first second := by
    ext i j
    rcases i with i | (i|i) <;> rcases j with j | (j|j) <;>
      simp [barrierVariation,Matrix.transpose_add,Matrix.mul_add,Matrix.add_mul,
        add_comm]
  map_smul' scalar perturbation := by
    ext i j
    rcases i with i | (i|i) <;> rcases j with j | (j|j) <;>
      simp [barrierVariation,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_mul,
        Matrix.smul_apply]

def variationFunctional (multiplier : K → ℝ) : Matrix K I ℝ →L[ℝ]
    Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ :=
  LinearMap.toContinuousLinearMap (variationLinear multiplier)

def inputHiddenBlock (matrix : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ) : Matrix I K ℝ :=
  matrix.toBlocks₁₂.toCols₁
def hiddenInputBlock (matrix : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ) : Matrix K I ℝ :=
  matrix.toBlocks₂₁.toRows₁

def frobeniusLinear (gradient : Matrix K I ℝ) : Matrix K I ℝ →ₗ[ℝ] ℝ where
  toFun perturbation := Matrix.trace (gradientᵀ*perturbation)
  map_add' first second := by simp [Matrix.mul_add,Matrix.trace_add]
  map_smul' scalar perturbation := by simp [Matrix.mul_smul,Matrix.trace_smul]

def frobeniusFunctional (gradient : Matrix K I ℝ) : Matrix K I ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (frobeniusLinear gradient)

theorem actual_barrier_matrix_weight_derivative (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (firstWeight : Matrix K I ℝ) :
    HasFDerivAt (barrierMatrix lastWeight multiplier gain)
      (variationFunctional (O := O) multiplier) firstWeight := by
  have he : barrierMatrix lastWeight multiplier gain=
      fun weight : Matrix K I ℝ => barrierMatrix lastWeight multiplier gain (0 : Matrix K I ℝ)+
        variationFunctional (O := O) multiplier weight := by
    funext weight
    ext i j
    rcases i with i | (i|i) <;> rcases j with j | (j|j) <;>
      simp [barrierMatrix,variationFunctional,variationLinear,barrierVariation,
        Matrix.add_apply]
  rw [he]
  exact (variationFunctional (O := O) multiplier).hasFDerivAt.const_add
    (barrierMatrix lastWeight multiplier gain (0 : Matrix K I ℝ))

theorem trace_of_actual_block_matrix {A B : Type*} [Fintype A] [Fintype B]
    (first : Matrix A A ℝ) (upper : Matrix A B ℝ) (lower : Matrix B A ℝ)
    (last : Matrix B B ℝ) :
    Matrix.trace (Matrix.fromBlocks first upper lower last)=Matrix.trace first+Matrix.trace last := by
  simp [Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks]

theorem trace_of_actual_offdiagonal_product {A B : Type*} [Fintype A] [Fintype B]
    (matrix : Matrix (A ⊕ B) (A ⊕ B) ℝ) (upper : Matrix A B ℝ) (lower : Matrix B A ℝ) :
    Matrix.trace (matrix*Matrix.fromBlocks 0 upper lower 0)=
      Matrix.trace (matrix.toBlocks₁₂*lower)+Matrix.trace (matrix.toBlocks₂₁*upper) := by
  calc
    _ = Matrix.trace ((Matrix.fromBlocks matrix.toBlocks₁₁ matrix.toBlocks₁₂
        matrix.toBlocks₂₁ matrix.toBlocks₂₂)*Matrix.fromBlocks 0 upper lower 0) := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = _ := by
      rw [Matrix.fromBlocks_multiply,trace_of_actual_block_matrix]
      simp

theorem actual_variation_trace_splits_into_weight_blocks
    (matrix : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ)
    (multiplier : K → ℝ) (perturbation : Matrix K I ℝ) :
    Matrix.trace (matrix*barrierVariation (O := O) multiplier perturbation)=
      -Matrix.trace (inputHiddenBlock matrix*Matrix.diagonal multiplier*perturbation)-
        Matrix.trace (hiddenInputBlock matrix*perturbationᵀ*Matrix.diagonal multiplier) := by
  unfold barrierVariation
  rw [trace_of_actual_offdiagonal_product]
  have hfirst : matrix.toBlocks₁₂*Matrix.fromRows (-(Matrix.diagonal multiplier*perturbation))
      (0 : Matrix O I ℝ)=inputHiddenBlock matrix*(-(Matrix.diagonal multiplier*perturbation)) := by
    calc
      _ = Matrix.fromCols matrix.toBlocks₁₂.toCols₁ matrix.toBlocks₁₂.toCols₂*
          Matrix.fromRows (-(Matrix.diagonal multiplier*perturbation)) (0 : Matrix O I ℝ) := by
        rw [Matrix.fromCols_toCols]
      _ = _ := by rw [Matrix.fromCols_mul_fromRows]; simp [inputHiddenBlock]
  have hsecond : Matrix.trace (matrix.toBlocks₂₁*Matrix.fromCols
      (-(perturbationᵀ*Matrix.diagonal multiplier)) (0 : Matrix I O ℝ))=
      Matrix.trace (hiddenInputBlock matrix*(-(perturbationᵀ*Matrix.diagonal multiplier))) := by
    calc
      _ = Matrix.trace (Matrix.fromRows matrix.toBlocks₂₁.toRows₁ matrix.toBlocks₂₁.toRows₂*
          Matrix.fromCols (-(perturbationᵀ*Matrix.diagonal multiplier)) (0 : Matrix I O ℝ)) := by
        rw [Matrix.fromRows_toRows]
      _ = _ := by rw [Matrix.fromRows_mul_fromCols,trace_of_actual_block_matrix]; simp [hiddenInputBlock]
  rw [hfirst,hsecond]
  simp [Matrix.mul_neg,Matrix.trace_neg,Matrix.mul_assoc]
  ring

theorem actual_symmetric_variation_trace_is_gradient
    (matrix : Matrix (I ⊕ (K ⊕ O)) (I ⊕ (K ⊕ O)) ℝ) (hsymmetric : matrix.IsSymm)
    (multiplier : K → ℝ) (perturbation : Matrix K I ℝ) :
    Matrix.trace (matrix*barrierVariation (O := O) multiplier perturbation)=
      Matrix.trace (((-2:ℝ) • (Matrix.diagonal multiplier*hiddenInputBlock matrix))ᵀ*perturbation) := by
  have hblocks : (hiddenInputBlock matrix)ᵀ=inputHiddenBlock matrix := by
    ext i k
    exact hsymmetric.apply (Sum.inl i) (Sum.inr (Sum.inl k))
  have hsecond : Matrix.trace (hiddenInputBlock matrix*perturbationᵀ*Matrix.diagonal multiplier)=
      Matrix.trace (inputHiddenBlock matrix*Matrix.diagonal multiplier*perturbation) := by
    rw [← Matrix.trace_transpose,Matrix.transpose_mul,Matrix.transpose_mul,
      Matrix.diagonal_transpose,Matrix.transpose_transpose,hblocks]
    rw [← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle (Matrix.diagonal multiplier) perturbation (inputHiddenBlock matrix)
  rw [actual_variation_trace_splits_into_weight_blocks,hsecond]
  rw [Matrix.transpose_smul,Matrix.transpose_mul,Matrix.diagonal_transpose,hblocks,
    Matrix.smul_mul,Matrix.trace_smul,Matrix.mul_assoc]
  simp
  ring

theorem actual_logdet_barrier_weight_gradient (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain : ℝ) (firstWeight : Matrix K I ℝ)
    (hpositive : (barrierMatrix lastWeight multiplier gain firstWeight).PosDef) :
    HasFDerivAt (fun weight : Matrix K I ℝ =>
      Real.log (barrierMatrix lastWeight multiplier gain weight).det)
      (frobeniusFunctional ((-2:ℝ) • (Matrix.diagonal multiplier*
        hiddenInputBlock ((barrierMatrix lastWeight multiplier gain firstWeight)⁻¹)))) firstWeight := by
  have hdet := hpositive.det_pos.ne'
  have h := (actual_logdet_has_frechet_derivative _ hdet).comp firstWeight
    (actual_barrier_matrix_weight_derivative lastWeight multiplier gain firstWeight)
  have he : traceProductFunctional (barrierMatrix lastWeight multiplier gain firstWeight)⁻¹ ∘L
      variationFunctional (O := O) multiplier=
      frobeniusFunctional ((-2:ℝ) • (Matrix.diagonal multiplier*
        hiddenInputBlock ((barrierMatrix lastWeight multiplier gain firstWeight)⁻¹))) := by
    ext perturbation
    exact actual_symmetric_variation_trace_is_gradient _ hpositive.inv.isHermitian.isSymm multiplier perturbation
  rw [← he]
  exact h

theorem actual_barrier_training_weight_gradient (lastWeight : Matrix O K ℝ)
    (multiplier : K → ℝ) (gain mu : ℝ) (firstWeight lossGradient : Matrix K I ℝ)
    (loss : Matrix K I ℝ → ℝ)
    (hloss : HasFDerivAt loss (frobeniusFunctional lossGradient) firstWeight)
    (hpositive : (barrierMatrix lastWeight multiplier gain firstWeight).PosDef) :
    HasFDerivAt (fun weight : Matrix K I ℝ => loss weight-
      mu*Real.log (barrierMatrix lastWeight multiplier gain weight).det)
      (frobeniusFunctional (lossGradient+(2*mu) • (Matrix.diagonal multiplier*
        hiddenInputBlock ((barrierMatrix lastWeight multiplier gain firstWeight)⁻¹)))) firstWeight := by
  have h := hloss.sub ((actual_logdet_barrier_weight_gradient lastWeight multiplier gain firstWeight
    hpositive).const_smul mu)
  have he : frobeniusFunctional lossGradient-mu •
      frobeniusFunctional ((-2:ℝ) • (Matrix.diagonal multiplier*
        hiddenInputBlock ((barrierMatrix lastWeight multiplier gain firstWeight)⁻¹)))=
      frobeniusFunctional (lossGradient+(2*mu) • (Matrix.diagonal multiplier*
        hiddenInputBlock ((barrierMatrix lastWeight multiplier gain firstWeight)⁻¹))) := by
    ext perturbation
    simp [frobeniusFunctional,frobeniusLinear,Matrix.transpose_add,Matrix.transpose_smul,
      Matrix.add_mul,Matrix.smul_mul,Matrix.trace_add,Matrix.trace_smul]
    ring
  rw [← he]
  exact h

end SafeLearning.CompleteModulesBarrierGradient
