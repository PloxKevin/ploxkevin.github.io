import SafeLearning.CompleteModulesLandscapeVectorMixture
import SafeLearning.CompleteModulesSafeOptKernelPosteriorError

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeKernelFeatures
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteModulesLandscapeVectorMixture
open CompleteModulesSafeOptGPInformationBudget CompleteFoundationsSequentialLogDet
open CompleteFoundationsTemporalLogDet

variable {X feature : Type*} [Fintype X] [DecidableEq X] [Fintype feature] [DecidableEq feature]

def queriedFeatures {Ω : Type*} (features : X → feature → ℝ) (query : ℕ → Ω → X)
    (i : ℕ) (omega : Ω) : feature → ℝ := features (query i omega)

def finiteNoise {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : Fin n → ℝ :=
  fun i => Y i omega

/-- A normalized finite PSD kernel has actual real features with every
coordinate bounded by one; the bound is derived from its diagonal norm. -/
theorem actual_normalized_finite_psd_kernel_has_coordinate_bounded_features
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) :
    ∃ features : X → X → ℝ,
      (∀ x y, kernel x y = features x ⬝ᵥ features y) ∧
      ∀ x j, |features x j| ≤ 1 := by
  obtain ⟨features, hf⟩ := actual_finite_positive_semidefinite_kernel_has_real_features kernel hkernel
  refine ⟨features, hf, ?_⟩
  intro x j
  have hs : (features x j) ^ 2 ≤ features x ⬝ᵥ features x := by
    simpa only [dotProduct, pow_two] using
      Finset.single_le_sum (fun k _ => sq_nonneg (features x k)) (Finset.mem_univ j)
  have hsq : (features x j) ^ 2 ≤ 1 := hs.trans (by rw [← hf]; exact hnormalized x)
  have h := (sq_le_sq₀ (abs_nonneg (features x j)) zero_le_one).mp
    (by simpa only [sq_abs, one_pow] using hsq)
  exact h

/-- On an actual finite measurable design space, a predictable query
gives predictable feature coordinates without an extra feature measurability premise. -/
theorem actual_predictable_finite_queries_give_predictable_feature_coordinates
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (F : Filtration ℕ mΩ) (features : X → feature → ℝ) (query : ℕ → Ω → X)
    (hq : ∀ i, Measurable[F i] (query i)) :
    ∀ i j, StronglyMeasurable[F i] (fun omega => queriedFeatures features query i omega j) := by
  intro i j
  exact ((measurable_of_countable (fun x : X => features x j)).comp (hq i)).stronglyMeasurable

/-- The actual accumulated feature-noise vector equals the transpose of
the actual finite query-feature matrix applied to the same observed noises. -/
theorem actual_query_feature_noise_sum_is_the_actual_transposed_sample_matrix
    {Ω : Type*} (features : X → feature → ℝ) (query : ℕ → Ω → X)
    (Y : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) :
    featureNoiseSum (queriedFeatures features query) Y n omega =
      (temporalFeatures (fun i => features (query i omega)) n)ᵀ *ᵥ finiteNoise Y n omega := by
  ext j
  simp only [featureNoiseSum, queriedFeatures, partialSum, temporalFeatures, finiteNoise,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i => features (query i omega) j * Y i omega) n).symm

/-- The actual cumulative outer-product matrix is the actual sample
feature Gram, for every finite horizon and arbitrary repeated queries. -/
theorem actual_query_cumulative_feature_gram_is_the_actual_sample_feature_gram
    {Ω : Type*} (features : X → feature → ℝ) (query : ℕ → Ω → X)
    (n : ℕ) (omega : Ω) :
    featureQuadraticGram (queriedFeatures features query) n omega =
      featureGram (temporalFeatures (fun i => features (query i omega)) n) := by
  ext j k
  simp only [featureQuadraticGram, queriedFeatures, partialSum, featureGram, temporalFeatures,
    Matrix.mul_apply, Matrix.transpose_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i => features (query i omega) j * features (query i omega) k) n).symm

/-- The same repeated-query sample matrix yields exactly the kernel Gram
used in the posterior formulas, rather than an independently chosen matrix. -/
theorem actual_query_sample_kernel_gram_is_the_actual_past_kernel_gram
    {Ω : Type*} (kernel : X → X → ℝ) (features : X → feature → ℝ)
    (hf : ∀ x y, kernel x y = features x ⬝ᵥ features y) (query : ℕ → Ω → X)
    (n : ℕ) (omega : Ω) :
    kernelGram (temporalFeatures (fun i => features (query i omega)) n) =
      actualKernelPastGram kernel (fun i => query i omega) n := by
  ext i j
  change features (query i omega) ⬝ᵥ features (query j omega) = kernel (query i omega) (query j omega)
  exact (hf _ _).symm

end SafeLearning.CompleteModulesLandscapeKernelFeatures

#print axioms SafeLearning.CompleteModulesLandscapeKernelFeatures.actual_normalized_finite_psd_kernel_has_coordinate_bounded_features
#print axioms SafeLearning.CompleteModulesLandscapeKernelFeatures.actual_predictable_finite_queries_give_predictable_feature_coordinates
#print axioms SafeLearning.CompleteModulesLandscapeKernelFeatures.actual_query_feature_noise_sum_is_the_actual_transposed_sample_matrix
#print axioms SafeLearning.CompleteModulesLandscapeKernelFeatures.actual_query_cumulative_feature_gram_is_the_actual_sample_feature_gram
#print axioms SafeLearning.CompleteModulesLandscapeKernelFeatures.actual_query_sample_kernel_gram_is_the_actual_past_kernel_gram
