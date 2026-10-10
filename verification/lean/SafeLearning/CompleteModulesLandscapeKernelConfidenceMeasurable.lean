import SafeLearning.CompleteModulesLandscapeKernelFeatures

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeKernelConfidenceMeasurable
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology BigOperators
open CompleteModulesSafeOptGPInformationBudget CompleteModulesSafeOptKernelPosteriorError

variable {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Finite measurable query tuples derive measurability of the actual GP
mean, variance, and normalized determinant. This does not need an assumed
measurable inverse-matrix formula or independent queries. -/
theorem actual_finite_query_kernel_posterior_mean_variance_and_determinant_are_measurable
    {Ω : Type*} [MeasurableSpace Ω] (kernel : X → X → ℝ) (lambda : ℝ)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (f : X → ℝ) (n : ℕ) (x : X) :
    Measurable (fun omega => actualKernelMeanAt kernel lambda (fun i => query i omega)
      f (fun i => Y i omega) n x) ∧
    Measurable (fun omega => actualKernelVarianceAt kernel lambda (fun i => query i omega) n x) ∧
    Measurable (fun omega => (1 + lambda⁻¹ • actualKernelPastGram kernel
      (fun i => query i omega) n).det) := by
  let design : Ω → Fin n → X := fun omega i => query i omega
  have hd : Measurable design := measurable_pi_lambda (fun i => hq i)
  have hi : ∀ i j : Fin n, Measurable (fun omega =>
      (lambda • 1 + actualKernelPastGram kernel (fun k => query k omega) n)⁻¹ i j) := by
    intro i j
    exact (measurable_of_countable (fun d : Fin n → X =>
      (lambda • 1 + Matrix.of (fun k l => kernel (d k) (d l)))⁻¹ i j)).comp hd
  have hc : ∀ i : Fin n, Measurable (fun omega => kernel x (query i omega)) :=
    fun i => (measurable_of_countable (kernel x)).comp (hq i)
  have hf : ∀ i : Fin n, Measurable (fun omega => f (query i omega) + Y i omega) :=
    fun i => ((measurable_of_countable f).comp (hq i)).add (hY i)
  refine ⟨?_, ?_, ?_⟩
  · unfold actualKernelMeanAt actualKernelCrossAt Matrix.mulVec dotProduct
    apply Finset.measurable_sum
    intro i hj
    apply (hc i).mul
    apply Finset.measurable_sum
    intro j hj
    exact (hi i j).mul (hf j)
  · unfold actualKernelVarianceAt actualKernelCrossAt Matrix.mulVec dotProduct
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro i hj
    apply (hc i).mul
    apply Finset.measurable_sum
    intro j hj
    exact (hi i j).mul (hc j)
  · exact (measurable_of_countable (fun d : Fin n → X =>
      (1 + lambda⁻¹ • Matrix.of (fun k l => kernel (d k) (d l))).det)).comp hd

/-- The actual all-time, every-input posterior confidence band is a
measurable event under the primitive predictable-query and next-noise
measurability assumptions used to derive its probability bound. -/
theorem actual_predictable_finite_kernel_posterior_band_event_is_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ) (lambda : ℝ) (query : ℕ → Ω → X)
    (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (f : X → ℝ) (B R delta : ℝ) :
    MeasurableSet {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega)
          f (fun i => Y i omega) n x| ≤
        (Real.sqrt B + R / Real.sqrt lambda *
          Real.sqrt (Real.log (1 + lambda⁻¹ • actualKernelPastGram kernel
            (fun i => query i omega) n).det + 2 * Real.log (1 / delta))) *
          Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} := by
  have hq' : ∀ i, Measurable (query i) := fun i => (hq i).mono (F.le i) le_rfl
  have hY' : ∀ i, Measurable (Y i) := fun i => ((hY i).mono (F.le (i + 1))).measurable
  have heq : {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) f (fun i => Y i omega) n x| ≤
        (Real.sqrt B + R / Real.sqrt lambda *
          Real.sqrt (Real.log (1 + lambda⁻¹ • actualKernelPastGram kernel (fun i => query i omega) n).det +
            2 * Real.log (1 / delta))) *
          Real.sqrt (actualKernelVarianceAt kernel lambda (fun i => query i omega) n x)} =
      ⋂ n, ⋂ x, {omega |
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) f (fun i => Y i omega) n x| ≤
        (Real.sqrt B + R / Real.sqrt lambda *
          Real.sqrt (Real.log (1 + lambda⁻¹ • actualKernelPastGram kernel (fun i => query i omega) n).det +
            2 * Real.log (1 / delta))) *
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
  apply measurableSet_le
  · exact (measurable_const.sub h.1).abs
  · exact (measurable_const.add ((h.2.2.log.add_const (2 * Real.log (1 / delta))).sqrt.const_mul
      (R / Real.sqrt lambda))).mul h.2.1.sqrt

end SafeLearning.CompleteModulesLandscapeKernelConfidenceMeasurable
