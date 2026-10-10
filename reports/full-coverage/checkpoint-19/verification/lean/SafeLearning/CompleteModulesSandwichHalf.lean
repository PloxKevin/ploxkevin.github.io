import SafeLearning.CompleteModulesSandwich

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSandwichHalf
open CompleteModulesSandwich

variable {I K O : Type*} [Fintype I] [Fintype K] [Fintype O]
    [DecidableEq I] [DecidableEq K] [DecidableEq O]

def actualHalfMultiplier (scale : K → ℝ) : K → ℝ := fun coordinate => scale coordinate^2/2

def actualHalfSchur (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ) (scale : K → ℝ) : Matrix K K ℝ :=
  (2:ℝ) • Matrix.diagonal (actualHalfMultiplier scale)-
    (actualSandwichOutput outputBlock scale)ᵀ*actualSandwichOutput outputBlock scale-
    Matrix.diagonal (actualHalfMultiplier scale)*actualSandwichInput inputBlock scale*
      (actualSandwichInput inputBlock scale)ᵀ*Matrix.diagonal (actualHalfMultiplier scale)

theorem actual_half_multiplier_is_half_of_full_multiplier (scale : K → ℝ) :
    Matrix.diagonal (actualHalfMultiplier scale)=(1/2:ℝ) • Matrix.diagonal (actualSandwichMultiplier scale) := by
  ext row column
  by_cases he : row=column
  · subst column
    simp [actualHalfMultiplier,actualSandwichMultiplier]
    ring
  · simp [actualHalfMultiplier,actualSandwichMultiplier,he]

theorem actual_half_sandwich_source_schur_expression
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    actualHalfSchur outputBlock inputBlock scale=
      Matrix.diagonal scale*((1/2:ℝ) • (1 : Matrix K K ℝ)-
        (3/2:ℝ) • (outputBlock*outputBlockᵀ))*Matrix.diagonal scale := by
  unfold actualHalfSchur
  simp only [actual_half_multiplier_is_half_of_full_multiplier,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  have hi := actual_sandwich_multiplier_input_gram inputBlock scale hscale
  have ho := actual_sandwich_output_gram outputBlock scale
  rw [hi,ho]
  simp only [smul_smul]
  rw [actual_sandwich_multiplier_is_square]
  have hb : inputBlock*inputBlockᵀ=1-outputBlock*outputBlockᵀ := by
    exact eq_sub_of_add_eq' hrows
  rw [hb]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_smul,Matrix.smul_mul]
  ext row column
  simp only [Matrix.sub_apply,Matrix.smul_apply]
  ring

theorem actual_half_multiplier_is_negative_when_output_gram_exceeds_one_third
    (outputBlock : Matrix K O ℝ) (inputBlock : Matrix K I ℝ)
    (hrows : outputBlock*outputBlockᵀ+inputBlock*inputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (hgram : (outputBlock*outputBlockᵀ-(1/3:ℝ) • (1 : Matrix K K ℝ)).PosDef) :
    (-(actualHalfSchur outputBlock inputBlock scale)).PosDef := by
  rw [actual_half_sandwich_source_schur_expression outputBlock inputBlock hrows scale hscale]
  have hu := CompleteModulesSLL.actual_positive_diagonal_is_invertible scale hscale
  have hp : (Matrix.diagonal scale*(outputBlock*outputBlockᵀ-(1/3:ℝ) • (1 : Matrix K K ℝ))*
      Matrix.diagonal scale).PosDef := by
    have hc := hu.posDef_star_left_conjugate_iff.mpr hgram
    simpa only [star_eq_conjTranspose,Matrix.diagonal_conjTranspose,star_trivial] using hc
  have hs := hp.smul (show (0:ℝ) < 3/2 by norm_num)
  convert hs using 1
  ext row column
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.neg_apply,Matrix.sub_apply,Matrix.smul_apply]
  ring

theorem actual_orthogonal_zero_input_half_schur_is_negative_square
    (outputBlock : Matrix K O ℝ) (hrows : outputBlock*outputBlockᵀ=(1 : Matrix K K ℝ))
    (scale : K → ℝ) (hscale : ∀ coordinate,0 < scale coordinate) :
    actualHalfSchur outputBlock (0 : Matrix K I ℝ) scale=
      -(Matrix.diagonal (actualSandwichMultiplier scale)) := by
  have hrow : outputBlock*outputBlockᵀ+(0 : Matrix K I ℝ)*(0 : Matrix K I ℝ)ᵀ=1 := by simp [hrows]
  rw [actual_half_sandwich_source_schur_expression outputBlock 0 hrow scale hscale,hrows,
    actual_sandwich_multiplier_is_square]
  ext row column
  by_cases he : row=column
  · subst column
    simp [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,actualSandwichMultiplier,pow_two]
    ring
  · simp [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,actualSandwichMultiplier,he]

end SafeLearning.CompleteModulesSandwichHalf
