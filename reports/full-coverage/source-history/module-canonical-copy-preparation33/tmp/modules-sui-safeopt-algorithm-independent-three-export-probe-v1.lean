import SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteModulesLandscapeSuiSafeOptSafety CompleteModulesLandscapeSuiSafeOptProbability
open CompleteModulesLandscapeSafeOptMeasurable CompleteModulesLandscapeSafeOptQueryProtocol
open CompleteModulesSafeOptFiniteOptimality CompleteModulesSafeOptInitializedRun

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]



example
    (f : X → ℝ) (constant : ℝ≥0) (hf : LipschitzWith constant f) (threshold : ℝ)
    (seed : Set X) (hseed_nonempty : seed.Nonempty) (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x))
    (query : ℕ → X)
    (hprotocol : ∀ n
      (hs : (actualInitializedSafeFinset seed threshold rawLower constant n).Nonempty)
      (hb : ∀ x ∈ actualInitializedSafeFinset seed threshold rawLower constant n,
        actualContainedLower seed threshold rawLower n x ≤ actualContainedUpper rawUpper n x),
      query n = actualFiniteQuery (actualInitializedSafeFinset seed threshold rawLower constant n)
        (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
        (fun x y => (constant : ℝ) * dist x y) threshold hs hb) :
    (∀ n, threshold ≤ f (query n)) ∧
      ∀ n x, x ∈ actualInitializedSafeFinset seed threshold rawLower constant n → threshold ≤ f x := by
  apply SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_initialized_width_maximizing_protocol_is_safe_on_true_raw_bands <;> assumption


variable {H : Type*} [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]



example
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (f : H) (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1)
    (constant : ℝ≥0) (hf : LipschitzWith constant (fun x => f x)) (threshold : ℝ)
    (seed : Set X) (hseed_nonempty : seed.Nonempty) (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hprotocol : ∀ omega n
      (hs : (actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n).Nonempty)
      (hb : ∀ x ∈ actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n,
        actualContainedLower seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n x ≤
          actualContainedUpper
            (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n x),
      query n omega = actualFiniteQuery
        (actualInitializedSafeFinset seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n)
        (actualContainedLower seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n)
        (actualContainedUpper
          (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n)
        (fun x y => (constant : ℝ) * dist x y) threshold hs hb) :
    MeasurableSet {omega | (∀ n, threshold ≤ f (query n omega)) ∧
      ∀ n x, x ∈ actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n →
          threshold ≤ f x} ∧
      1 - delta ≤ μ.real {omega | (∀ n, threshold ≤ f (query n omega)) ∧
        ∀ n x, x ∈ actualInitializedSafeFinset seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n →
            threshold ≤ f x} := by
  apply SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_source_beta_width_maximizing_safeopt_has_one_measurable_alltime_safety_event <;> assumption


example
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (f : H) (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1)
    (constant : ℝ≥0) (hf : LipschitzWith constant (fun x => f x)) (threshold : ℝ)
    (seed : Set X) (hseed_nonempty : seed.Nonempty) (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hprotocol : ∀ omega n
      (hs : (actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n).Nonempty)
      (hb : ∀ x ∈ actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n,
        actualContainedLower seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n x ≤
          actualContainedUpper
            (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n x),
      query n omega = actualFiniteQuery
        (actualInitializedSafeFinset seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n)
        (actualContainedLower seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n)
        (actualContainedUpper
          (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) n)
        (fun x y => (constant : ℝ) * dist x y) threshold hs hb) :
    MeasurableSet {omega | ∀ n, threshold ≤ f (query n omega)} ∧
      1 - delta ≤ μ.real {omega | ∀ n, threshold ≤ f (query n omega)} := by
  apply SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_source_beta_width_maximizing_safeopt_alltime_query_safety_probability <;> assumption


end SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm

#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_initialized_width_maximizing_protocol_is_safe_on_true_raw_bands

#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_source_beta_width_maximizing_safeopt_has_one_measurable_alltime_safety_event

#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm.actual_source_beta_width_maximizing_safeopt_alltime_query_safety_probability
