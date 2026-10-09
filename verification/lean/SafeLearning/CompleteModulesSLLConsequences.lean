import SafeLearning.CompleteModulesSLL

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSLLConsequences

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M]

def actualHiddenIncrement (weights : Matrix M N ℝ) (activation : ℝ → ℝ)
    (bias : N → ℝ) (first second : M → ℝ) : N → ℝ :=
  fun coordinate => activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
    activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)

theorem actual_sll_input_output_increment
    (weights : Matrix M N ℝ) (diagonal : N → ℝ) (activation : ℝ → ℝ)
    (bias : N → ℝ) (first second : M → ℝ) :
    SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias first-
      SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias second=
      (first-second)-(2:ℝ) • (weights*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥ
        actualHiddenIncrement weights activation bias first second)) := by
  unfold SafeLearning.CompleteModulesSLL.actualSLL actualHiddenIncrement
  have hh : (fun coordinate => activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
      activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate))=
      (fun coordinate => activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate))-
        (fun coordinate => activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)) := rfl
  rw [hh,Matrix.mulVec_sub,Matrix.mulVec_sub]
  module

theorem actual_inverse_certificate_pullback_is_source_quadratic
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate, 0<diagonal coordinate) (hidden : N → ℝ) :
    hidden ⬝ᵥ(((Matrix.diagonal diagonal)⁻¹*(Matrix.diagonal diagonal-weightsᵀ*weights)*
      (Matrix.diagonal diagonal)⁻¹)*ᵥhidden)=
      ((Matrix.diagonal diagonal)⁻¹*ᵥhidden) ⬝ᵥ
        ((Matrix.diagonal diagonal-weightsᵀ*weights)*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥhidden)) := by
  have hs : ((Matrix.diagonal diagonal)⁻¹)ᵀ=(Matrix.diagonal diagonal)⁻¹ := by
    simp [SafeLearning.CompleteModulesSLL.actual_positive_diagonal_inverse diagonal hpositive]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  conv_lhs => rw [← hs,Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm,hs]

theorem actual_sll_source_energy_margin
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate, 0<diagonal coordinate)
    (hcertificate : (Matrix.diagonal diagonal-weightsᵀ*weights).PosSemidef)
    (activation : ℝ → ℝ)
    (hactivation : SafeLearning.CompleteModulesLipSDP.slopeRestricted activation 0 1)
    (bias : N → ℝ) (first second : M → ℝ) :
    let hidden := actualHiddenIncrement weights activation bias first second
    let remainder := (4:ℝ)*(hidden ⬝ᵥ
      (((Matrix.diagonal diagonal)⁻¹*(Matrix.diagonal diagonal-weightsᵀ*weights)*
        (Matrix.diagonal diagonal)⁻¹)*ᵥhidden))
    remainder≤‖WithLp.toLp 2 (first-second)‖^2-
      ‖WithLp.toLp 2 (SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias first-
        SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias second)‖^2 ∧
      0≤remainder := by
  let hidden := actualHiddenIncrement weights activation bias first second
  let direction := (Matrix.diagonal diagonal)⁻¹*ᵥhidden
  have he := SafeLearning.CompleteModulesSLL.actual_sll_energy_gap_is_qc_plus_certificate
    weights diagonal hpositive (first-second) hidden
  have hq := SafeLearning.CompleteModulesSLL.actual_sll_incremental_quadratic_constraint
    weights diagonal hpositive activation hactivation bias first second
  have hr := hcertificate.dotProduct_mulVec_nonneg direction
  simp only [star_trivial] at hr
  dsimp only
  rw [actual_sll_input_output_increment,actual_inverse_certificate_pullback_is_source_quadratic
    weights diagonal hpositive]
  change 0≤hidden ⬝ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥ
    (weightsᵀ*ᵥ(first-second)-hidden)) at hq
  change 0≤((Matrix.diagonal diagonal)⁻¹*ᵥhidden) ⬝ᵥ
    ((Matrix.diagonal diagonal-weightsᵀ*weights)*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥhidden)) at hr
  change (4:ℝ)*(((Matrix.diagonal diagonal)⁻¹*ᵥhidden) ⬝ᵥ
    ((Matrix.diagonal diagonal-weightsᵀ*weights)*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥhidden)))≤_ ∧
    0≤(4:ℝ)*(((Matrix.diagonal diagonal)⁻¹*ᵥhidden) ⬝ᵥ
    ((Matrix.diagonal diagonal-weightsᵀ*weights)*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥhidden)))
  constructor <;> nlinarith

theorem actual_majorizer_diagonal_is_nonnegative
    (weights : Matrix M N ℝ) (scale : N → ℝ)
    (hscale : ∀ coordinate, 0<scale coordinate) (coordinate : N) :
    0≤SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal (weightsᵀ*weights) scale coordinate := by
  unfold SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal
  exact Finset.sum_nonneg (fun column _ => div_nonneg
    (mul_nonneg (abs_nonneg _) (hscale column).le) (hscale coordinate).le)

theorem actual_majorizer_diagonal_is_positive_for_nonzero_column
    (weights : Matrix M N ℝ) (scale : N → ℝ)
    (hscale : ∀ coordinate, 0<scale coordinate) (coordinate : N)
    (hcolumn : ∃ row, weights row coordinate≠0) :
    0<SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal (weightsᵀ*weights) scale coordinate := by
  have hgram : 0<(weightsᵀ*weights) coordinate coordinate := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    obtain ⟨row,hrow⟩ := hcolumn
    exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _) ⟨row,Finset.mem_univ _,mul_self_pos.mpr hrow⟩
  have hbound := Finset.single_le_sum
    (fun column (_ : column ∈ Finset.univ) => div_nonneg
      (mul_nonneg (abs_nonneg ((weightsᵀ*weights) coordinate column)) (hscale column).le)
        (hscale coordinate).le) (Finset.mem_univ coordinate)
  have hself : |(weightsᵀ*weights) coordinate coordinate| * scale coordinate/scale coordinate=
      (weightsᵀ*weights) coordinate coordinate := by
    rw [abs_of_pos hgram,mul_div_cancel_right₀ _ (hscale coordinate).ne']
  rw [hself] at hbound
  exact hgram.trans_le hbound

theorem actual_positive_regularization_makes_majorizer_diagonal_positive
    (weights : Matrix M N ℝ) (scale : N → ℝ)
    (hscale : ∀ coordinate, 0<scale coordinate) (epsilon : ℝ) (hepsilon : 0<epsilon)
    (coordinate : N) :
    0<SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal (weightsᵀ*weights) scale coordinate+epsilon := by
  have h := actual_majorizer_diagonal_is_nonnegative weights scale hscale coordinate
  linarith

theorem actual_source_scaled_sll_is_nonexpansive
    (weights : Matrix M N ℝ) (scale : N → ℝ)
    (hscale : ∀ coordinate, 0<scale coordinate)
    (hcolumns : ∀ coordinate, ∃ row, weights row coordinate≠0)
    (activation : ℝ → ℝ)
    (hactivation : SafeLearning.CompleteModulesLipSDP.slopeRestricted activation 0 1)
    (bias : N → ℝ) (first second : M → ℝ) :
    let diagonal := SafeLearning.CompleteModulesScaledGram.actualMajorizerDiagonal (weightsᵀ*weights) scale
    ‖WithLp.toLp 2 (SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias first-
      SafeLearning.CompleteModulesSLL.actualSLL weights diagonal activation bias second)‖≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  apply SafeLearning.CompleteModulesSLL.actual_sll_is_euclidean_nonexpansive
  · intro coordinate
    exact actual_majorizer_diagonal_is_positive_for_nonzero_column weights scale hscale coordinate (hcolumns coordinate)
  · exact SafeLearning.CompleteModulesScaledGram.actual_weighted_gram_matrix_is_bounded_by_source_diagonal
      weights scale hscale
  · exact hactivation

end SafeLearning.CompleteModulesSLLConsequences
