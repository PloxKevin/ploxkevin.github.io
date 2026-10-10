import SafeLearning.CompleteModulesLandscapeKernelConfidenceMeasurable
import SafeLearning.CompleteModulesLandscapeInformationIndexing
import SafeLearning.CompleteModulesLandscapeZeroNoisePosterior

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

/-- The true attained repeated-design maximum has nonnegative information,
derived from its actual maximizing design and PSD sequential log factors. -/
theorem actual_finite_psd_kernel_attained_maximum_information_is_nonnegative
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (t : ℕ) :
    0 ≤ actualFiniteMaximumKernelInformationGain kernel lambda t := by
  obtain ⟨design, hdesign⟩ :=
    (actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design
      kernel lambda t).1
  rw [← hdesign]
  exact actual_finite_psd_kernel_every_repeated_design_information_is_nonnegative
    kernel hkernel lambda hlambda t design

/-- For every source round n+1, the literal source beta dominates the
squared-norm bias. This includes the first round with zero observations. -/
theorem actual_source_beta_square_root_dominates_the_squared_norm_square_root
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (B : ℝ) (hB : 0 ≤ B)
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) (n : ℕ) :
    Real.sqrt B ≤
      Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
        (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) := by
  have hround : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hratio : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / delta :=
    (le_div_iff₀ hd).mpr (by simpa using hdone.le.trans hround)
  have hlog : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ) / delta) := Real.log_nonneg hratio
  have hGamma := actual_finite_psd_kernel_attained_maximum_information_is_nonnegative
    kernel hkernel lambda hlambda (n + 1)
  apply Real.sqrt_le_sqrt
  have hterm : 0 ≤ 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
      (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3 := by positivity
  linarith

omit [Nonempty X] in
/-- The all-round, every-input event with the literal source beta is
measurable. Its round n+1 radius uses exactly n actual past observations. -/
theorem actual_predictable_finite_kernel_source_beta_posterior_event_is_measurable
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
  have hq' : ∀ i, Measurable (query i) := fun i => (hq i).mono (F.le i) le_rfl
  have hY' : ∀ i, Measurable (Y i) := fun i => ((hY i).mono (F.le (i + 1))).measurable
  have heq : {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) f (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} =
      ⋂ n, ⋂ x, {omega |
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) f (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} := by
    ext omega
    simp
  rw [heq]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro x
  have h := actual_finite_query_kernel_posterior_mean_variance_and_determinant_are_measurable
    kernel lambda query hq' Y hY' f n x
  exact measurableSet_le (measurable_const.sub h.1).abs (measurable_const.mul h.2.1.sqrt)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- Actual zero-width noise support derives the literal source beta band
almost everywhere for arbitrary outcome-dependent queries and positive lambda. -/
theorem actual_zero_width_noise_has_the_source_beta_posterior_band_almost_everywhere
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
  have hPSD := actual_finite_rkhs_kernel_is_positive_semidefinite kernel hkernel
  have hBnonnegative : 0 ≤ B := (sq_nonneg ‖f‖).trans hB
  have he := actual_zero_width_noise_support_gives_one_common_alltime_kernel_posterior_event
    μ kernel hkernel lambda hlambda query f B hB Y hY
  filter_upwards [he] with omega hw
  intro n x
  apply (hw.2.2 n x).trans
  exact mul_le_mul_of_nonneg_right
    (actual_source_beta_square_root_dominates_the_squared_norm_square_root
      kernel hPSD lambda hlambda B hBnonnegative delta hd hdone n) (Real.sqrt_nonneg _)

/-- With positive regularization and zero-width noise, the same literal
source beta event has probability one, including zero observations. -/
theorem actual_zero_width_noise_source_beta_posterior_event_has_probability_one
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
  have he := actual_zero_width_noise_has_the_source_beta_posterior_band_almost_everywhere
    μ kernel hkernel lambda hlambda query f B hB Y hY delta hd hdone
  calc
    _ = μ univ := measure_congr (by
      filter_upwards [he] with omega hw
      exact propext (iff_true_intro hw))
    _ = 1 := measure_univ

end SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary
