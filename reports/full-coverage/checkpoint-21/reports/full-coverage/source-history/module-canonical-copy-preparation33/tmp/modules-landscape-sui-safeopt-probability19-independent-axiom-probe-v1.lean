import SafeLearning.CompleteModulesLandscapeSuiSafeOptSafety
import SafeLearning.CompleteModulesLandscapeSafeOptMeasurable

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteModulesLandscapeSuiSafeOptSafety CompleteModulesLandscapeSafeOptMeasurable
open CompleteModulesLandscapeKernelConfidenceMeasurable
open CompleteModulesSafeOptGPInformationBudget CompleteModulesSafeOptKernelPosteriorError
open CompleteModulesSafeOptInitializedRun

variable {X H : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- The same literal source raw GP lower endpoint is measurable from the
primitive adapted query and next-noise data. -/
theorem actual_source_beta_raw_lower_endpoint_is_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ) (lambda B delta : ℝ)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (f : X → ℝ) (round : ℕ) (x : X) :
    Measurable (fun omega => actualSourceRawLower kernel lambda B delta
      (fun i => query i omega) f (fun i => Y i omega) round x) := by
  have hq' : ∀ i, Measurable (query i) := fun i => (hq i).mono (F.le i) le_rfl
  have hY' : ∀ i, Measurable (Y i) := fun i => ((hY i).mono (F.le (i + 1))).measurable
  have hm := actual_finite_query_kernel_posterior_mean_variance_and_determinant_are_measurable
    kernel lambda query hq' Y hY' f (round - 1) x
  exact hm.1.sub (measurable_const.mul hm.2.1.sqrt)

variable [PseudoMetricSpace X]

/-- The genuine primitive assumptions imply a measurable simultaneous event
protecting every learning query and every point of every actually computed
seed-initialized/intersected/expanded safe set. -/
theorem actual_source_beta_learning_queries_and_computed_safe_sets_have_one_measurable_safety_event
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
    (hquery : ∀ omega n, query n omega ∈ actualInitializedSafeFinset seed threshold
      (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n) :
    MeasurableSet {omega | (∀ n, threshold ≤ f (query n omega)) ∧
      ∀ n x, x ∈ actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n →
          threshold ≤ f x} ∧
      1 - delta ≤ μ.real {omega | (∀ n, threshold ≤ f (query n omega)) ∧
        ∀ n x, x ∈ actualInitializedSafeFinset seed threshold
          (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n →
            threshold ≤ f x} := by
  constructor
  · exact actual_initialized_query_and_every_safe_round_safety_event_is_measurable
      (fun x => f x) seed threshold constant
      (fun omega => actualSourceRawLower kernel lambda B delta
        (fun i => query i omega) (fun x => f x) (fun i => Y i omega))
      (fun n x => actual_source_beta_raw_lower_endpoint_is_measurable
        F kernel lambda B delta query hq Y hY (fun x => f x) n x)
      query (fun i => (hq i).mono (F.le i) le_rfl)
  · exact actual_source_beta_initialized_safeopt_learning_queries_are_safe_with_one_joint_probability
      μ F kernel hkernel query hq Y hY R hYb hz lambda hlambda hscale f B hB delta hd hdone
      constant hf threshold seed hseed_nonempty hseed hquery

/-- Projection of the same common event gives the literal measurable
all-time query-safety probability, with no independence assumption. -/
theorem actual_source_beta_alltime_learning_query_safety_probability
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
    (hquery : ∀ omega n, query n omega ∈ actualInitializedSafeFinset seed threshold
      (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n) :
    MeasurableSet {omega | ∀ n, threshold ≤ f (query n omega)} ∧
      1 - delta ≤ μ.real {omega | ∀ n, threshold ≤ f (query n omega)} := by
  constructor
  · have heq : {omega | ∀ n, threshold ≤ f (query n omega)} =
        ⋂ n, {omega | threshold ≤ f (query n omega)} := by ext omega; simp
    rw [heq]
    exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const
      ((measurable_of_countable (fun x => f x)).comp ((hq n).mono (F.le n) le_rfl)))
  · apply (actual_source_beta_initialized_safeopt_learning_queries_are_safe_with_one_joint_probability
      μ F kernel hkernel query hq Y hY R hYb hz lambda hlambda hscale f B hB delta hd hdone
      constant hf threshold seed hseed_nonempty hseed hquery).trans
    exact measureReal_mono (fun _ hw => hw.1) (measure_ne_top μ _)

end SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability

#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability.actual_source_beta_raw_lower_endpoint_is_measurable
#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability.actual_source_beta_learning_queries_and_computed_safe_sets_have_one_measurable_safety_event
#print axioms SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability.actual_source_beta_alltime_learning_query_safety_probability
