import SafeLearning.CompleteModulesSLLRegularization

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesAOL
open CompleteModulesScaledGram CompleteModulesSLL CompleteModulesLipSDP

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M]

def actualInverseSquareRootDiagonal (diagonal : N → ℝ) : Matrix N N ℝ :=
  Matrix.diagonal (fun coordinate => 1/Real.sqrt (diagonal coordinate))

def actualRescaledLinearLayer (weights : Matrix M N ℝ) (diagonal : N → ℝ) (input : N → ℝ) : M → ℝ :=
  weights*ᵥ(actualInverseSquareRootDiagonal diagonal*ᵥinput)

theorem actual_inverse_square_root_diagonal_is_symmetric (diagonal : N → ℝ) :
    (actualInverseSquareRootDiagonal diagonal)ᵀ=actualInverseSquareRootDiagonal diagonal := by
  simp [actualInverseSquareRootDiagonal]

theorem actual_inverse_square_root_normalizes_diagonal
    (diagonal : N → ℝ) (hpositive : ∀ coordinate,0 < diagonal coordinate) :
    actualInverseSquareRootDiagonal diagonal*Matrix.diagonal diagonal*
      actualInverseSquareRootDiagonal diagonal=(1 : Matrix N N ℝ) := by
  ext row column
  unfold actualInverseSquareRootDiagonal
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases he : row=column
  · subst column
    have hs := Real.sq_sqrt (hpositive row).le
    have hp := Real.sqrt_pos.mpr (hpositive row)
    simp only [Matrix.diagonal_apply,if_true,Matrix.one_apply_eq]
    field_simp
    nlinarith
  · simp [Matrix.diagonal_apply,Matrix.one_apply,he]

theorem actual_rescaled_linear_layer_coordinate_energy
    (weights : Matrix M N ℝ) (diagonal : N → ℝ) (input : N → ℝ) :
    (∑ row,(actualRescaledLinearLayer weights diagonal input row)^2)=
      (actualInverseSquareRootDiagonal diagonal*ᵥinput) ⬝ᵥ
        ((weightsᵀ*weights)*ᵥ(actualInverseSquareRootDiagonal diagonal*ᵥinput)) := by
  unfold actualRescaledLinearLayer
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro row hrow
  ring

theorem actual_positive_diagonal_normalized_energy
    (diagonal : N → ℝ) (hpositive : ∀ coordinate,0 < diagonal coordinate) (input : N → ℝ) :
    (actualInverseSquareRootDiagonal diagonal*ᵥinput) ⬝ᵥ
      (Matrix.diagonal diagonal*ᵥ(actualInverseSquareRootDiagonal diagonal*ᵥinput))=
      ∑ coordinate,(input coordinate)^2 := by
  have hs := actual_inverse_square_root_diagonal_is_symmetric diagonal
  have hn := actual_inverse_square_root_normalizes_diagonal diagonal hpositive
  have hp : input ⬝ᵥ((actualInverseSquareRootDiagonal diagonal*Matrix.diagonal diagonal*
      actualInverseSquareRootDiagonal diagonal)*ᵥinput)=
      (actualInverseSquareRootDiagonal diagonal*ᵥinput) ⬝ᵥ
        (Matrix.diagonal diagonal*ᵥ(actualInverseSquareRootDiagonal diagonal*ᵥinput)) := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
    conv_lhs => rw [← hs,Matrix.dotProduct_transpose_mulVec]
    rw [dotProduct_comm,hs]
  rw [← hp,hn,Matrix.one_mulVec]
  simp only [dotProduct,pow_two]

theorem actual_positive_diagonal_gram_certificate_implies_rescaled_energy_bound
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate,0 < diagonal coordinate)
    (hcertificate : (Matrix.diagonal diagonal-weightsᵀ*weights).PosSemidef)
    (input : N → ℝ) :
    (∑ row,(actualRescaledLinearLayer weights diagonal input row)^2) ≤
      ∑ coordinate,(input coordinate)^2 := by
  have hc := hcertificate.dotProduct_mulVec_nonneg (actualInverseSquareRootDiagonal diagonal*ᵥinput)
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub] at hc
  rw [actual_positive_diagonal_normalized_energy diagonal hpositive input] at hc
  rw [actual_rescaled_linear_layer_coordinate_energy]
  linarith

theorem actual_source_rescaled_linear_layer_is_nonexpansive
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate,0 < diagonal coordinate)
    (hcertificate : (Matrix.diagonal diagonal-weightsᵀ*weights).PosSemidef)
    (first second : N → ℝ) :
    ‖WithLp.toLp 2 (actualRescaledLinearLayer weights diagonal first-
      actualRescaledLinearLayer weights diagonal second)‖ ≤ ‖WithLp.toLp 2 (first-second)‖ := by
  have hinc : actualRescaledLinearLayer weights diagonal first-actualRescaledLinearLayer weights diagonal second=
      actualRescaledLinearLayer weights diagonal (first-second) := by
    simp [actualRescaledLinearLayer,Matrix.mulVec_sub]
  have he := actual_positive_diagonal_gram_certificate_implies_rescaled_energy_bound weights diagonal
    hpositive hcertificate (first-second)
  rw [hinc]
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at he
  nlinarith [norm_nonneg (WithLp.toLp 2 (actualRescaledLinearLayer weights diagonal (first-second))),
    norm_nonneg (WithLp.toLp 2 (first-second))]

end SafeLearning.CompleteModulesAOL
