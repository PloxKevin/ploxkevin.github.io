import SafeLearning.CompleteAppliedGaussianEntropy

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedGaussianEntropyConsequences
open MeasureTheory ProbabilityTheory
open scoped NNReal
open SafeLearning.CompleteAppliedGaussianEntropy

def negativeEntropyVariance : ℝ≥0 :=
  ⟨Real.exp (-3) / (2 * Real.pi), by positivity⟩

theorem actual_negative_entropy_variance_positive : 0 < negativeEntropyVariance := by
  change 0 < Real.exp (-3) / (2 * Real.pi)
  positivity

theorem actual_probability_density_with_negative_entropy (mean : ℝ) :
    IsProbabilityMeasure (gaussianReal mean negativeEntropyVariance) ∧
    (∀ x : ℝ, 0 < gaussianPDFReal mean negativeEntropyVariance x) ∧
    -(∫ x : ℝ, gaussianPDFReal mean negativeEntropyVariance x *
      Real.log (gaussianPDFReal mean negativeEntropyVariance x)) = -1 := by
  have hv : negativeEntropyVariance ≠ 0 := ne_of_gt actual_negative_entropy_variance_positive
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    exact gaussianPDFReal_pos _ _ _ hv
  · rw [← actual_gaussian_density_entropy_integral _ _ hv,
      actual_gaussian_differential_entropy _ _ hv]
    have he : 2 * Real.pi * Real.exp 1 * (negativeEntropyVariance : ℝ) = Real.exp (-2) := by
      change 2 * Real.pi * Real.exp 1 * (Real.exp (-3) / (2 * Real.pi)) = _
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.exp_add]
      field_simp
    rw [he, Real.log_exp]
    norm_num

def scaledVariance (scale : ℝ) (variance : ℝ≥0) : ℝ≥0 :=
  ⟨scale ^ 2, sq_nonneg scale⟩ * variance

theorem actual_nonzero_scaling_variance_nonzero {scale : ℝ} {variance : ℝ≥0}
    (hs : scale ≠ 0) (hv : variance ≠ 0) : scaledVariance scale variance ≠ 0 := by
  apply mul_ne_zero _ hv
  intro h
  have he : scale ^ 2 = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  exact hs (sq_eq_zero_iff.mp he)

theorem actual_scaled_gaussian_law (mean : ℝ) (variance : ℝ≥0) (scale : ℝ) :
    (gaussianReal mean variance).map (fun x => scale * x) =
      gaussianReal (scale * mean) (scaledVariance scale variance) := by
  exact gaussianReal_map_const_mul scale

theorem actual_scaled_gaussian_entropy {scale : ℝ} (hs : scale ≠ 0)
    (mean : ℝ) (variance : ℝ≥0) (hv : variance ≠ 0) :
    gaussianDifferentialEntropy (scale * mean) (scaledVariance scale variance) =
      gaussianDifferentialEntropy mean variance + Real.log |scale| := by
  rw [actual_gaussian_differential_entropy _ _ (actual_nonzero_scaling_variance_nonzero hs hv),
      actual_gaussian_differential_entropy _ _ hv]
  have hc : 0 < 2 * Real.pi * Real.exp 1 * (variance : ℝ) := by
    have hp : 0 < (variance : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    positivity
  have he : 2 * Real.pi * Real.exp 1 * (scaledVariance scale variance : ℝ) =
      (2 * Real.pi * Real.exp 1 * (variance : ℝ)) * scale ^ 2 := by
    change 2 * Real.pi * Real.exp 1 * (scale ^ 2 * (variance : ℝ)) = _
    ring
  rw [he, Real.log_mul (ne_of_gt hc) (pow_ne_zero 2 hs), Real.log_pow, Real.log_abs]
  ring

theorem actual_scaled_density_entropy_integral {scale : ℝ} (hs : scale ≠ 0)
    (mean : ℝ) (variance : ℝ≥0) (hv : variance ≠ 0) :
    -(∫ x : ℝ, gaussianPDFReal (scale * mean) (scaledVariance scale variance) x *
      Real.log (gaussianPDFReal (scale * mean) (scaledVariance scale variance) x)) =
      -(∫ x : ℝ, gaussianPDFReal mean variance x *
        Real.log (gaussianPDFReal mean variance x)) + Real.log |scale| := by
  rw [← actual_gaussian_density_entropy_integral _ _ (actual_nonzero_scaling_variance_nonzero hs hv),
    ← actual_gaussian_density_entropy_integral _ _ hv]
  exact actual_scaled_gaussian_entropy hs mean variance hv

end SafeLearning.CompleteAppliedGaussianEntropyConsequences
