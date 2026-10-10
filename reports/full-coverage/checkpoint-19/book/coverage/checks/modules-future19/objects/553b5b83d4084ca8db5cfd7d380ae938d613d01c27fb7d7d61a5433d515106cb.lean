import SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteModulesLandscapeKernelConfidenceMeasurable CompleteModulesLandscapeInformationIndexing
open CompleteModulesLandscapeZeroNoisePosterior CompleteModulesSafeOptGPInformationBudget
open CompleteModulesSafeOptKernelPosteriorError

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]



example
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (t : ℕ) :
    0 ≤ actualFiniteMaximumKernelInformationGain kernel lambda t := by
  apply SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_finite_psd_kernel_attained_maximum_information_is_nonnegative <;> assumption


example
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (B : ℝ) (hB : 0 ≤ B)
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) (n : ℕ) :
    Real.sqrt B ≤
      Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
        (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) := by
  apply SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_source_beta_square_root_dominates_the_squared_norm_square_root <;> assumption


omit [Nonempty X] in
example
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ) (lambda : ℝ) (query : ℕ → Ω → X)
    (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (f : X → ℝ) (B delta : ℝ) :
    MeasurableSet {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega)
          f (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} := by
  apply SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_predictable_finite_kernel_source_beta_posterior_event_is_measurable <;> assumption


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ]



example
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → Ω → X) (f : H)
    (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0)
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    ∀ᵐ omega ∂μ, ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega)
          (fun y => f y) (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x) := by
  apply SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_zero_width_noise_has_the_source_beta_posterior_band_almost_everywhere <;> assumption


example
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → Ω → X) (f : H)
    (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0)
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    μ {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega)
          (fun y => f y) (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} = 1 := by
  apply SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_zero_width_noise_source_beta_posterior_event_has_probability_one <;> assumption


end SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary

#print axioms SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_finite_psd_kernel_attained_maximum_information_is_nonnegative

#print axioms SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_source_beta_square_root_dominates_the_squared_norm_square_root

#print axioms SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_predictable_finite_kernel_source_beta_posterior_event_is_measurable

#print axioms SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_zero_width_noise_has_the_source_beta_posterior_band_almost_everywhere

#print axioms SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary.actual_zero_width_noise_source_beta_posterior_event_has_probability_one
