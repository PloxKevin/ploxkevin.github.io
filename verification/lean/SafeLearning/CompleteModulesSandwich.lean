import SafeLearning.CompleteModulesBarrierSoundness
import SafeLearning.CompleteModulesSLL

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSandwich
open CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesBarrierGradient CompleteModulesBarrierSoundness

variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

def actualSandwichInput (block : Matrix K I ℝ) (scale : K → ℝ) : Matrix K I ℝ :=
  Real.sqrt 2 • ((Matrix.diagonal scale)⁻¹*block)

def actualSandwichOutput (block : Matrix K O ℝ) (scale : K → ℝ) : Matrix O K ℝ :=
  Real.sqrt 2 • (blockᵀ*Matrix.diagonal scale)

def actualSandwichMultiplier (scale : K → ℝ) : K → ℝ := fun coordinate => scale coordinate^2

theorem actual_sandwich_multiplier_is_square (scale : K → ℝ) :
    Matrix.diagonal (actualSandwichMultiplier scale)=Matrix.diagonal scale*Matrix.diagonal scale := by
  ext row column
  rw [Matrix.diagonal_mul]
  by_cases he : row=column
  · subst column
    simp [actualSandwichMultiplier,pow_two]
  · simp [actualSandwichMultiplier,he]

theorem actual_sandwich_output_gram (outputBlock : Matrix K O ℝ) (scale : K → ℝ) :
    (actualSandwichOutput outputBlock scale)ᵀ*actualSandwichOutput outputBlock scale=
      (2:ℝ) • (Matrix.diagonal scale*(outputBlock*outputBlockᵀ)*Matrix.diagonal scale) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold actualSandwichOutput
  simp only [Matrix.transpose_smul,Matrix.transpose_mul,Matrix.diagonal_transpose,
    Matrix.transpose_transpose,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [show Real.sqrt (2:ℝ)*Real.sqrt 2=2 by nlinarith]
  congr 1
  simp only [Matrix.mul_assoc]

theorem actual_sandwich_multiplier_input_gram
    (inputBlock : Matrix K I ℝ) (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    Matrix.diagonal (actualSandwichMultiplier scale)*actualSandwichInput inputBlock scale*
      (actualSandwichInput inputBlock scale)ᵀ*Matrix.diagonal (actualSandwichMultiplier scale)=
      (2:ℝ) • (Matrix.diagonal scale*(inputBlock*inputBlockᵀ)*Matrix.diagonal scale) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu := CompleteModulesSLL.actual_positive_diagonal_is_invertible scale hscale
  have hdet := (Matrix.isUnit_iff_isUnit_det (Matrix.diagonal scale)).mp hu
  have hi := Matrix.mul_nonsing_inv (Matrix.diagonal scale) hdet
  have his := Matrix.nonsing_inv_mul (Matrix.diagonal scale) hdet
  have hsym : ((Matrix.diagonal scale)⁻¹)ᵀ=(Matrix.diagonal scale)⁻¹ := by
    rw [CompleteModulesSLL.actual_positive_diagonal_inverse scale hscale]
    simp
  unfold actualSandwichInput
  simp only [actual_sandwich_multiplier_is_square]
  simp only [Matrix.transpose_smul,Matrix.transpose_mul,hsym,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  rw [show Real.sqrt (2:ℝ)*Real.sqrt 2=2 by nlinarith]
  congr 1
  calc
    _ = Matrix.diagonal scale*(Matrix.diagonal scale*(Matrix.diagonal scale)⁻¹)*
        (inputBlock*inputBlockᵀ)*((Matrix.diagonal scale)⁻¹*Matrix.diagonal scale)*
          Matrix.diagonal scale := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hi,his];simp [Matrix.mul_assoc]

theorem actual_sandwich_source_schur_expression_is_zero
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    (2:ℝ) • Matrix.diagonal (actualSandwichMultiplier scale)-
      (actualSandwichOutput outputBlock scale)ᵀ*actualSandwichOutput outputBlock scale-
      Matrix.diagonal (actualSandwichMultiplier scale)*actualSandwichInput inputBlock scale*
        (actualSandwichInput inputBlock scale)ᵀ*Matrix.diagonal (actualSandwichMultiplier scale)=0 := by
  rw [actual_sandwich_output_gram,actual_sandwich_multiplier_input_gram inputBlock scale hscale,
    actual_sandwich_multiplier_is_square]
  have he : Matrix.diagonal scale*Matrix.diagonal scale-
      Matrix.diagonal scale*(outputBlock*outputBlockᵀ)*Matrix.diagonal scale-
      Matrix.diagonal scale*(inputBlock*inputBlockᵀ)*Matrix.diagonal scale=
      Matrix.diagonal scale*((1 : Matrix K K ℝ)-
        (outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ))*Matrix.diagonal scale := by noncomm_ring
  rw [← smul_sub,← smul_sub,he,hrows]
  simp

end SafeLearning.CompleteModulesSandwich
