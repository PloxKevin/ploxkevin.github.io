import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteModulesGPNoiseDomains

theorem actual_source_bounded_zero_mean_noise_has_subgaussian_scale_one_tenth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hmeas : AEMeasurable X P)
    (hbound : ∀ᵐ omega ∂P, X omega ∈ Icc (-(1/10 : ℝ)) (1/10))
    (hmean : ∫ omega, X omega ∂P = 0) :
    HasSubgaussianMGF X (1/100 : ℝ≥0) P := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hbound hmean
  have he : ((‖(1/10 : ℝ) - -(1/10)‖₊ / 2)^2 : ℝ≥0) = 1/100 := by
    ext
    norm_num
  simpa only [he] using h

theorem actual_any_nondegenerate_gaussian_noise_is_not_almost_surely_bounded
    (mean : ℝ) (variance : ℝ≥0) (hv : variance ≠ 0) (bound : ℝ) :
    ¬ (∀ᵐ x ∂gaussianReal mean variance, |x| ≤ bound) := by
  intro hbound
  have hnull := (ae_iff.mp hbound)
  have hsub : Ioi bound ⊆ {x : ℝ | ¬ |x| ≤ bound} := by
    intro x hx h
    have hx' : bound < x := hx
    linarith [le_abs_self x]
  have htail : (gaussianReal mean variance) (Ioi bound) = 0 :=
    measure_mono_null hsub hnull
  have hvolume := gaussianReal_absolutelyContinuous' mean hv htail
  simp only [Real.volume_Ioi] at hvolume
  exact ENNReal.top_ne_zero hvolume

theorem actual_source_nondegenerate_gaussian_noise_cannot_have_the_bounded_noise_domain
    (variance : ℝ≥0) (hv : variance ≠ 0) :
    ¬ (∀ᵐ x ∂gaussianReal 0 variance, x ∈ Icc (-(1/10 : ℝ)) (1/10)) := by
  intro h
  apply actual_any_nondegenerate_gaussian_noise_is_not_almost_surely_bounded 0 variance hv (1/10)
  filter_upwards [h] with x hx
  exact abs_le.mpr hx

end SafeLearning.CompleteModulesGPNoiseDomains
