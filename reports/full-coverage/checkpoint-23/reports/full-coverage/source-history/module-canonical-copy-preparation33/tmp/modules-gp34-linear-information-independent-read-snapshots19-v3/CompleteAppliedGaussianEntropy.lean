import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedGaussianEntropy
open MeasureTheory ProbabilityTheory
open scoped NNReal

def gaussianDifferentialEntropy (mean : ℝ) (variance : ℝ≥0) : ℝ :=
  -(∫ x, Real.log (gaussianPDFReal mean variance x) ∂gaussianReal mean variance)

theorem actual_gaussian_log_density (mean : ℝ) (variance : ℝ≥0)
    (hv : variance ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal mean variance x) =
      -Real.log (2 * Real.pi * variance) / 2 - (x - mean) ^ 2 / (2 * variance) := by
  have hp : 0 < (variance : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : 0 < 2 * Real.pi * (variance : ℝ) := by positivity
  rw [gaussianPDFReal, Real.log_mul (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc)))
    (ne_of_gt (Real.exp_pos _)), Real.log_inv, Real.log_sqrt hc.le, Real.log_exp]
  ring

theorem actual_gaussian_centered_square_integrable (mean : ℝ) (variance : ℝ≥0) :
    Integrable (fun x : ℝ => (x - mean) ^ 2) (gaussianReal mean variance) := by
  have hi : MemLp (fun x : ℝ => x - mean) 2 (gaussianReal mean variance) := by
    convert (memLp_id_gaussianReal' (μ := mean) (v := variance) 2 (by norm_num)).sub
        (memLp_const mean) using 1
    funext x
    rfl
  exact hi.integrable_sq

theorem actual_gaussian_log_density_integrable (mean : ℝ) (variance : ℝ≥0)
    (hv : variance ≠ 0) :
    Integrable (fun x => Real.log (gaussianPDFReal mean variance x))
      (gaussianReal mean variance) := by
  have he : (fun x => Real.log (gaussianPDFReal mean variance x)) =
      (fun x => -Real.log (2 * Real.pi * variance) / 2 -
        (x - mean) ^ 2 / (2 * variance)) := by
    funext x
    exact actual_gaussian_log_density mean variance hv x
  rw [he]
  exact (integrable_const _).sub
    ((actual_gaussian_centered_square_integrable mean variance).div_const _)

theorem actual_gaussian_centered_square_integral (mean : ℝ) (variance : ℝ≥0) :
    (∫ x : ℝ, (x - mean) ^ 2 ∂gaussianReal mean variance) = variance := by
  have h := variance_eq_integral (μ := gaussianReal mean variance)
    (X := id) measurable_id'.aemeasurable
  simpa only [variance_id_gaussianReal, integral_id_gaussianReal, id_eq] using h.symm

theorem actual_gaussian_density_entropy_integral (mean : ℝ) (variance : ℝ≥0)
    (hv : variance ≠ 0) :
    gaussianDifferentialEntropy mean variance =
      -(∫ x : ℝ, gaussianPDFReal mean variance x *
        Real.log (gaussianPDFReal mean variance x)) := by
  unfold gaussianDifferentialEntropy
  rw [integral_gaussianReal_eq_integral_smul hv]
  rfl

theorem actual_gaussian_differential_entropy (mean : ℝ) (variance : ℝ≥0)
    (hv : variance ≠ 0) :
    gaussianDifferentialEntropy mean variance =
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * variance) := by
  have hp : 0 < (variance : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : 0 < 2 * Real.pi * (variance : ℝ) := by positivity
  have he : (fun x => Real.log (gaussianPDFReal mean variance x)) =
      (fun x => -Real.log (2 * Real.pi * variance) / 2 -
        (x - mean) ^ 2 / (2 * variance)) := by
    funext x
    exact actual_gaussian_log_density mean variance hv x
  have hl : Real.log (2 * Real.pi * Real.exp 1 * (variance : ℝ)) =
      Real.log (2 * Real.pi * (variance : ℝ)) + 1 := by
    have hm : 2 * Real.pi * Real.exp 1 * (variance : ℝ) =
        (2 * Real.pi * variance) * Real.exp 1 := by ring
    rw [hm, Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  unfold gaussianDifferentialEntropy
  rw [he, integral_sub (integrable_const _)
      ((actual_gaussian_centered_square_integrable mean variance).div_const _),
    integral_const, integral_div, actual_gaussian_centered_square_integral, hl]
  simp only [probReal_univ, one_smul]
  field_simp
  ring

end SafeLearning.CompleteAppliedGaussianEntropy
