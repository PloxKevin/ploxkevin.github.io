import SafeLearning.CompleteModulesGPExamples
import SafeLearning.CompleteModulesGPDesign
import SafeLearning.CompleteModulesKernelCorollaries
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesGPGradedLiteralBridges
open CompleteModulesGPExamples CompleteModulesKernel CompleteModulesKernelCorollaries

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem actual_two_kernel_sections_are_not_orthogonal_and_the_coefficient_norm_differs
    [CompleteSpace H] [RKHS ℝ H X ℝ] (a b : X)
    (haa : scalarKernel (H := H) a a = 1) (hbb : scalarKernel (H := H) b b = 1)
    (hab : scalarKernel (H := H) a b = 1 / 2) :
    inner ℝ (scalarSection (H := H) a) (scalarSection (H := H) b) ≠ 0 ∧
      ‖scalarSection (H := H) a - scalarSection (H := H) b‖ ^ 2 = 1 ∧
      ((1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) = 2 ∧
      ‖scalarSection (H := H) a - scalarSection (H := H) b‖ ^ 2 ≠
        ((1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) := by
  have hn := (section_difference_half (scalarSection (H := H) a)
    (scalarSection (H := H) b) haa hbb hab).2.2.1
  refine ⟨?_, hn, by norm_num, ?_⟩
  · change scalarKernel (H := H) a b ≠ 0
    rw [hab]
    norm_num
  · rw [hn]
    norm_num

theorem actual_variance_misuse_gives_the_printed_false_certificate_and_both_valid_band_witnesses :
    (1 : ℝ) - 3 * (4 / 100) = 88 / 100 ∧
      (1 : ℝ) + 3 * (4 / 100) = 112 / 100 ∧
      (1 / 2 : ℝ) < 88 / 100 ∧
      (2 / 5 : ℝ) ∈ Set.Icc (2 / 5) (8 / 5) ∧ (2 / 5 : ℝ) < 1 / 2 ∧
      (1 : ℝ) ∈ Set.Icc (2 / 5) (8 / 5) ∧ (1 / 2 : ℝ) ≤ 1 := by
  norm_num

theorem actual_confidence_multiplier_conversion_matches_all_half_widths
    (paperCoefficient moduleCoefficient : ℝ) :
    (∀ sigma : ℝ, 0 ≤ sigma →
      Real.sqrt paperCoefficient * sigma = moduleCoefficient * sigma) ↔
      moduleCoefficient = Real.sqrt paperCoefficient := by
  constructor
  · intro h
    simpa using (h 1 (by norm_num)).symm
  · intro h sigma hsigma
    rw [h]

theorem actual_singleton_interpolant_is_exact_at_the_observed_kernel_section
    [CompleteSpace H] [RKHS ℝ H X ℝ] (function : H) (a : X)
    (haa : scalarKernel (H := H) a a = 1) :
    ((function a) • scalarSection (H := H) a) a = function a := by
  rw [← scalar_section_reproduces ((function a) • scalarSection (H := H) a) a]
  rw [real_inner_smul_left]
  change function a * scalarKernel (H := H) a a = function a
  rw [haa, mul_one]

theorem actual_two_point_information_matrix_has_the_printed_shifted_eigenvectors :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) + twoGram (1 / 2)) *ᵥ ![1, 1] =
      (5 / 2 : ℝ) • ![1, 1] ∧
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) + twoGram (1 / 2)) *ᵥ ![1, -1] =
      (3 / 2 : ℝ) • ![1, -1] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [twoGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem actual_rkhs_conflicting_values_give_the_printed_cauchy_schwarz_bound
    [CompleteSpace H] [RKHS ℝ H X ℝ] (function : H) (a b : X) (r : ℝ)
    (haa : scalarKernel (H := H) a a = 1) (hbb : scalarKernel (H := H) b b = 1)
    (hab : scalarKernel (H := H) a b = r) (hfa : function a = 1) (hfb : function b = -1) :
    (2 : ℝ) ≤ ‖function‖ * Real.sqrt (2 * (1 - r)) := by
  have hsq := (section_difference_values (scalarSection (H := H) a)
    (scalarSection (H := H) b) r haa hbb hab).2.2
  have hb := abs_real_inner_le_norm function
    (scalarSection (H := H) a - scalarSection (H := H) b)
  rw [inner_sub_right, scalar_section_reproduces, scalar_section_reproduces,
    hfa, hfb] at hb
  have hn : Real.sqrt (2 * (1 - r)) =
      ‖scalarSection (H := H) a - scalarSection (H := H) b‖ := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hn]
  norm_num at hb
  exact hb

theorem actual_conflicting_norm_square_root_has_the_printed_rounding :
    |Real.sqrt 200 - (141421 / 10000 : ℝ)| < 1 / 20000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)
  have hp := Real.sqrt_nonneg (200 : ℝ)
  rw [abs_lt]
  constructor <;> nlinarith

theorem actual_fixed_sample_count_misspecification_certificate_tends_to_the_floor
    (epsilon beta correction : ℝ) :
    Tendsto (fun sigma : ℝ => epsilon + (beta + epsilon * correction) * sigma)
      (𝓝 0) (𝓝 epsilon) := by
  have hc : Continuous (fun sigma : ℝ => epsilon + (beta + epsilon * correction) * sigma) :=
    by fun_prop
  simpa only [mul_zero, add_zero] using hc.tendsto (0 : ℝ)

theorem actual_zero_posterior_variance_can_retain_a_positive_misspecification_error
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    |epsilon - 0| ≤ epsilon ∧ |(0 : ℝ) - 0| ≤ 2 * 0 ∧
      |(0 : ℝ) - 0| ≤ epsilon * 8 * 0 ∧ |epsilon - 0| = epsilon ∧
      ¬ |epsilon - 0| ≤ 2 * 0 := by
  simp [abs_of_pos hepsilon, hepsilon]

end SafeLearning.CompleteModulesGPGradedLiteralBridges
