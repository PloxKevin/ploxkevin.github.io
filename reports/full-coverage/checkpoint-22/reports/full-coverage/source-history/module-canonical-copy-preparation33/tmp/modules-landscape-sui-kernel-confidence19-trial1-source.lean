import SafeLearning.CompleteModulesLandscapeSuiFeatureConfidence
import SafeLearning.CompleteModulesLandscapeInformationIndexing
import SafeLearning.CompleteModulesLandscapeKernelConfidenceMeasurable

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiKernelConfidence
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteModulesLandscapeVectorMixture CompleteModulesLandscapeKernelFeatures
open CompleteModulesLandscapeSuiFeatureConfidence CompleteModulesLandscapeInformationIndexing
open CompleteModulesLandscapeSuiQuadratic CompleteModulesLandscapeKernelConfidenceMeasurable
open CompleteModulesSafeOptGPInformationBudget CompleteModulesSafeOptKernelPosteriorError
open CompleteModulesSafeOptPosteriorError CompleteFoundationsSequentialLogDet CompleteFoundationsTemporalLogDet

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The actual same-query kernel noise quadratic is nonnegative. Features
and the true regularized inverse are derived from the given finite PSD kernel. -/
theorem actual_finite_psd_kernel_noise_quadratic_is_nonnegative
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (lambda : ℝ) (hlambda : 0 < lambda) (query : ℕ → X) (noise : ℕ → ℝ) (n : ℕ) :
    0 ≤ actualKernelNoiseQuadratic kernel lambda query noise n := by
  obtain ⟨features, hf⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  let Phi := temporalFeatures (fun i => features (query i)) n
  have hG : (featureGram Phi).PosSemidef := by
    simpa only [featureGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Phi
  have hn := actual_positive_regularized_psd_inverse_quadratic_is_nonnegative
    (featureGram Phi) hG lambda hlambda (Phiᵀ *ᵥ (fun i : Fin n => noise i))
  change 0 ≤ actualFeatureNoiseQuadratic lambda Phi (fun i : Fin n => noise i) at hn
  rw [actual_feature_noise_quadratic_is_the_kernel_noise_quadratic lambda hlambda] at hn
  have hgram : kernelGram Phi = actualKernelPastGram kernel query n := by
    ext i j
    exact (hf (query i) (query j)).symm
  simpa only [noisyKernel, hgram, actualKernelNoiseQuadratic] using hn

variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The true attained finite repeated-design information maximum supplies
the deterministic schedule. Primitive predictable finite queries and bounded
conditionally centered noise then derive the literal 300 coefficient on
one common all-time event, at the same actual likelihood regularizer. -/
theorem actual_finite_psd_kernel_noise_has_the_source_information_log_cubed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    1 - delta ≤ μ.real {omega | ∀ n,
      2 * (actualKernelNoiseQuadratic kernel lambda (fun i => query i omega) (fun i => Y i omega) n / lambda) ≤
        300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3} := by
  obtain ⟨features, hf⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  let K : ℝ≥0 := ⟨∑ x, ∑ j, |features x j|, Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))⟩
  have hb : ∀ x j, |features x j| ≤ K := by
    intro x j
    have hrow : |features x j| ≤ ∑ k, |features x k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (features x k)) (Finset.mem_univ j)
    have hsum : (∑ k, |features x k|) ≤ ∑ y, ∑ k, |features y k| :=
      Finset.single_le_sum (fun y _ => Finset.sum_nonneg (fun k _ => abs_nonneg (features y k))) (Finset.mem_univ x)
    exact hrow.trans hsum
  have hp := actual_predictable_finite_queries_give_predictable_feature_coordinates F features query hq
  have hbound : ∀ i j, ∀ᵐ omega ∂μ, |queriedFeatures features query i omega j| ≤ K :=
    fun i j => Eventually.of_forall (fun omega => hb (query i omega) j)
  have hGamma : ∀ t, 0 ≤ actualFiniteMaximumKernelInformationGain kernel lambda t := by
    intro t
    obtain ⟨design, hdesign⟩ :=
      (actual_finite_maximum_kernel_information_gain_is_attained_and_bounds_every_design kernel lambda t).1
    rw [← hdesign]
    exact actual_finite_psd_kernel_every_repeated_design_information_is_nonnegative kernel hkernel lambda hlambda t design
  have hinfo : ∀ n omega,
      Real.log (1 + lambda⁻¹ • featureQuadraticGram (queriedFeatures features query) n omega).det ≤
        2 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) := by
    intro n omega
    rw [actual_query_cumulative_feature_gram_is_the_actual_sample_feature_gram]
    let Phi := temporalFeatures (fun i => features (query i omega)) n
    have hdet : (1 + lambda⁻¹ • kernelGram Phi).det = (1 + lambda⁻¹ • featureGram Phi).det := by
      simpa only [featureGram, kernelGram, Matrix.mul_smul, Matrix.smul_mul] using
        CompleteFoundationsUniversalMatrices.actual_sylvester_determinant_identity (lambda⁻¹ • Phi) Phiᵀ
    have hgram : kernelGram Phi = actualKernelPastGram kernel (fun i => query i omega) n := by
      ext i j
      exact (hf (query i omega) (query j omega)).symm
    have hn := actual_finite_psd_kernel_realized_information_is_bounded_by_the_next_round_maximum
      kernel hkernel lambda hlambda (fun i => query i omega) n
    change (1 / 2) * Real.log (1 + lambda⁻¹ • actualKernelPastGram kernel (fun i => query i omega) n).det ≤ _ at hn
    rw [← hgram, hdet] at hn
    change Real.log (1 + lambda⁻¹ • featureGram Phi).det ≤ _
    linarith
  have he := actual_alltime_feature_noise_has_the_source_information_log_cubed_budget μ F
    (queriedFeatures features query) Y hp hY K R hbound hYb hz hR lambda hlambda hscale
    (actualFiniteMaximumKernelInformationGain kernel lambda) hGamma hinfo delta hd hdone
  convert he using 2
  ext omega
  apply forall_congr'
  intro n
  rw [actual_query_feature_noise_sum_is_the_actual_transposed_sample_matrix,
    actual_query_cumulative_feature_gram_is_the_actual_sample_feature_gram]
  change (_ ≤ _) ↔ (2 * (actualFeatureNoiseQuadratic lambda
    (temporalFeatures (fun i => features (query i omega)) n) (finiteNoise Y n omega) / lambda) ≤ _)
  rw [actual_feature_noise_quadratic_is_the_kernel_noise_quadratic lambda hlambda]
  simp only [noisyKernel, actualKernelNoiseQuadratic, finiteNoise,
    actual_query_sample_kernel_gram_is_the_actual_past_kernel_gram kernel features hf query n omega]

/-- Actual RKHS squared-norm bias and the genuinely derived same-query
noise event give the source beta=2B+300Gamma_t log(t/delta)^3 band. Round
t=n+1 uses exactly n past observations and the true attained Gamma_t. -/
theorem actual_finite_rkhs_posterior_has_the_source_information_log_cubed_confidence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (f : H) (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    1 - delta ≤ μ.real {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y) (fun i => Y i omega) n x| ≤
        Real.sqrt (2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
          (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3) *
            Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} := by
  have hPSD := actual_finite_rkhs_kernel_is_positive_semidefinite kernel hkernel
  have he := actual_finite_psd_kernel_noise_has_the_source_information_log_cubed_budget μ F
    kernel hPSD query hq Y hY R hR hYb hz lambda hlambda hscale delta hd hdone
  apply he.trans
  apply measureReal_mono _ (measure_ne_top μ _)
  intro omega hw n x
  let Q := actualKernelNoiseQuadratic kernel lambda (fun i => query i omega) (fun i => Y i omega) n
  let C := 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
    (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3
  have hQ : 0 ≤ Q := actual_finite_psd_kernel_noise_quadratic_is_nonnegative
    kernel hPSD lambda hlambda (fun i => query i omega) (fun i => Y i omega) n
  have hn : 2 * (Q / lambda) ≤ C := hw n
  have hroot : (Real.sqrt Q / Real.sqrt lambda) ^ 2 = Q / lambda := by
    rw [div_pow, Real.sq_sqrt hQ, Real.sq_sqrt hlambda.le]
  have hsq : (‖f‖ + Real.sqrt Q / Real.sqrt lambda) ^ 2 ≤ 2 * B + C := by
    have hs := sq_nonneg (‖f‖ - Real.sqrt Q / Real.sqrt lambda)
    nlinarith
  apply (actual_finite_kernel_posterior_error_is_bounded_at_every_input_and_round kernel hkernel
    lambda hlambda (fun i => query i omega) f (fun i => Y i omega) n x).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.le_sqrt_of_sq_le hsq

end SafeLearning.CompleteModulesLandscapeSuiKernelConfidence
