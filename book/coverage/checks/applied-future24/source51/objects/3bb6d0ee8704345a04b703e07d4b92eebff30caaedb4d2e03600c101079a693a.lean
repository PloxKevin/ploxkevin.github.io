import SafeLearning.CompleteModulesSLLConsequences
import SafeLearning.CompleteModulesTheory
import Mathlib.Analysis.SpecialFunctions.Sigmoid

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSLLRegularization
open CompleteModulesSLL CompleteModulesSLLConsequences CompleteModulesScaledGram

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M]

def actualRegularizedDiagonal (weights : Matrix M N ℝ) (scale : N → ℝ) (epsilon : ℝ) : N → ℝ :=
  fun coordinate => actualMajorizerDiagonal (weightsᵀ*weights) scale coordinate+epsilon

theorem actual_regularized_certificate_is_positive_definite
    (weights : Matrix M N ℝ) (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (Matrix.diagonal (actualRegularizedDiagonal weights scale epsilon)-weightsᵀ*weights).PosDef := by
  have hpd : (Matrix.diagonal (fun (_ : N) => epsilon)).PosDef :=
    Matrix.PosDef.diagonal (fun _ => hepsilon)
  have hbase := actual_weighted_gram_matrix_is_bounded_by_source_diagonal weights scale hscale
  have he : Matrix.diagonal (actualRegularizedDiagonal weights scale epsilon)-weightsᵀ*weights=
      Matrix.diagonal (fun (_ : N) => epsilon)+(actualScaledMajorizer (weightsᵀ*weights) scale-weightsᵀ*weights) := by
    ext row column
    by_cases he : row=column
    · subst column
      simp [actualRegularizedDiagonal,actualScaledMajorizer,Matrix.diagonal_apply]
      ring
    · simp [actualRegularizedDiagonal,actualScaledMajorizer,Matrix.diagonal_apply,he]
  rw [he]
  exact hpd.add_posSemidef hbase

theorem actual_regularized_sll_is_nonexpansive
    (weights : Matrix M N ℝ) (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (activation : ℝ → ℝ)
    (hactivation : CompleteModulesLipSDP.slopeRestricted activation 0 1)
    (bias : N → ℝ) (first second : M → ℝ) :
    ‖WithLp.toLp 2 (actualSLL weights (actualRegularizedDiagonal weights scale epsilon) activation bias first-
      actualSLL weights (actualRegularizedDiagonal weights scale epsilon) activation bias second)‖ ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  apply actual_sll_is_euclidean_nonexpansive
  · intro coordinate
    exact actual_positive_regularization_makes_majorizer_diagonal_positive weights scale hscale
      epsilon hepsilon coordinate
  · exact (actual_regularized_certificate_is_positive_definite weights scale hscale epsilon hepsilon).posSemidef
  · exact hactivation

theorem actual_monotone_one_lipschitz_function_has_unit_interval_chords
    (activation : ℝ → ℝ) (hmono : Monotone activation) (hlip : LipschitzWith 1 activation) :
    CompleteModulesLipSDP.slopeRestricted activation 0 1 := by
  intro first second
  by_cases he : first=second
  · subst second
    exact ⟨0,by norm_num,by norm_num,by simp⟩
  · refine ⟨(activation first-activation second)/(first-second),?_,?_,?_⟩
    · rcases le_total second first with hs | hs
      · exact div_nonneg (sub_nonneg.mpr (hmono hs)) (sub_nonneg.mpr hs)
      · exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmono hs)) (sub_nonpos.mpr hs)
    · have hab := hlip.dist_le_mul first second
      simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hab
      have ha : |(activation first-activation second)/(first-second)| ≤ 1 := by
        rw [abs_div,div_le_one (abs_pos.mpr (sub_ne_zero.mpr he))]
        exact hab
      exact (le_abs_self _).trans ha
    · exact (div_mul_cancel₀ _ (sub_ne_zero.mpr he)).symm

theorem actual_tanh_has_unit_interval_chords :
    CompleteModulesLipSDP.slopeRestricted Real.tanh 0 1 :=
  actual_monotone_one_lipschitz_function_has_unit_interval_chords Real.tanh
    CompleteModulesTheory.tanh_monotone CompleteModulesTheory.tanh_lipschitz

theorem actual_sigmoid_derivative_is_in_quarter_interval (value : ℝ) :
    0 ≤ deriv Real.sigmoid value ∧ deriv Real.sigmoid value ≤ 1/4 := by
  rw [(Real.hasDerivAt_sigmoid value).deriv]
  have hl := Real.sigmoid_nonneg value
  have hu := Real.sigmoid_le_one value
  constructor
  · exact mul_nonneg hl (sub_nonneg.mpr hu)
  · nlinarith [sq_nonneg (Real.sigmoid value-1/2)]

theorem actual_sigmoid_is_one_lipschitz : LipschitzWith 1 Real.sigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro value
    exact (Real.hasDerivAt_sigmoid value).differentiableAt
  · intro value
    have hb := actual_sigmoid_derivative_is_in_quarter_interval value
    have hn : ‖deriv Real.sigmoid value‖ ≤ (1:ℝ) := by
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
      linarith
    exact_mod_cast hn

theorem actual_sigmoid_has_unit_interval_chords :
    CompleteModulesLipSDP.slopeRestricted Real.sigmoid 0 1 :=
  actual_monotone_one_lipschitz_function_has_unit_interval_chords Real.sigmoid
    Real.sigmoid_strictMono.monotone actual_sigmoid_is_one_lipschitz

theorem actual_regularized_sll_relu_tanh_sigmoid_are_nonexpansive
    (weights : Matrix M N ℝ) (scale : N → ℝ) (hscale : ∀ coordinate,0 < scale coordinate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (bias : N → ℝ) (first second : M → ℝ) :
    ∀ activation ∈ ({(fun value : ℝ => max value 0),Real.tanh,Real.sigmoid} : Set (ℝ → ℝ)),
      ‖WithLp.toLp 2 (actualSLL weights (actualRegularizedDiagonal weights scale epsilon) activation bias first-
        actualSLL weights (actualRegularizedDiagonal weights scale epsilon) activation bias second)‖ ≤
        ‖WithLp.toLp 2 (first-second)‖ := by
  intro activation hactivation
  have hs : CompleteModulesLipSDP.slopeRestricted activation 0 1 := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hactivation
    rcases hactivation with h | h | h
    · subst activation
      exact CompleteModulesLipSDP.relu_slope_restricted
    · subst activation
      exact actual_tanh_has_unit_interval_chords
    · subst activation
      exact actual_sigmoid_has_unit_interval_chords
  exact actual_regularized_sll_is_nonexpansive weights scale hscale epsilon hepsilon activation hs bias first second

end SafeLearning.CompleteModulesSLLRegularization
