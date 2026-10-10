import SafeLearning.CompleteModulesLandscapeSuiKernelConfidence
import SafeLearning.CompleteModulesLandscapeSuiZeroNoiseBoundary
import SafeLearning.CompleteModulesSafeOptInitializedRun

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiSafeOptSafety
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteModulesLandscapeSuiKernelConfidence CompleteModulesLandscapeSuiZeroNoiseBoundary
open CompleteModulesSafeOptGPInformationBudget CompleteModulesSafeOptKernelPosteriorError
open CompleteModulesSafeOptInitializedRun

variable {X H : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]

def actualSourceBeta (kernel : X → X → ℝ) (lambda B delta : ℝ) (n : ℕ) : ℝ :=
  2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda (n + 1) *
    (Real.log (((n + 1 : ℕ) : ℝ) / delta)) ^ 3

def actualSourceRadius (kernel : X → X → ℝ) (lambda B delta : ℝ)
    (query : ℕ → X) (n : ℕ) (x : X) : ℝ :=
  Real.sqrt (actualSourceBeta kernel lambda B delta n) *
    Real.sqrt (actualKernelVarianceAt kernel lambda query n x)

def actualSourceRawLower (kernel : X → X → ℝ) (lambda B delta : ℝ)
    (query : ℕ → X) (f : X → ℝ) (noise : ℕ → ℝ) (round : ℕ) (x : X) : ℝ :=
  actualKernelMeanAt kernel lambda query f noise (round - 1) x -
    actualSourceRadius kernel lambda B delta query (round - 1) x

def actualSourceRawUpper (kernel : X → X → ℝ) (lambda B delta : ℝ)
    (query : ℕ → X) (f : X → ℝ) (noise : ℕ → ℝ) (round : ℕ) (x : X) : ℝ :=
  actualKernelMeanAt kernel lambda query f noise (round - 1) x +
    actualSourceRadius kernel lambda B delta query (round - 1) x

/-- Including zero-width noise, primitive source noise assumptions derive
one genuine measurable all-round/every-input source-beta posterior event.
The regularizer is positive and at least the squared noise bound. -/
theorem actual_source_beta_posterior_confidence_includes_zero_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (kernel : X → X → ℝ)
    (hkernel : ∀ x y, kernel x y = CompleteModulesKernel.scalarKernel (H := H) x y)
    (query : ℕ → Ω → X) (hq : ∀ i, Measurable[F i] (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hYb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (hscale : (R : ℝ) ^ 2 ≤ lambda)
    (f : H) (B : ℝ) (hB : ‖f‖ ^ 2 ≤ B) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    MeasurableSet {omega | ∀ n x,
      |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y) (fun i => Y i omega) n x| ≤
        actualSourceRadius kernel lambda B delta (fun i => query i omega) n x} ∧
      1 - delta ≤ μ.real {omega | ∀ n x,
        |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y) (fun i => Y i omega) n x| ≤
          actualSourceRadius kernel lambda B delta (fun i => query i omega) n x} := by
  constructor
  · exact actual_predictable_finite_kernel_source_beta_posterior_event_is_measurable
      F kernel lambda query hq Y hY (fun x => f x) B delta
  · by_cases hR : 0 < (R : ℝ)
    · exact actual_finite_rkhs_posterior_has_the_source_information_log_cubed_confidence
        μ F kernel hkernel query hq Y hY R hR hYb hz lambda hlambda hscale f B hB delta hd hdone
    · have hzero : (R : ℝ) = 0 := le_antisymm (le_of_not_gt hR) R.coe_nonneg
      have hYzero : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc 0 0 := by
        simpa only [hzero, neg_zero] using hYb
      have he := actual_zero_width_noise_source_beta_posterior_event_has_probability_one
        μ kernel hkernel lambda hlambda query f B hB Y hYzero delta hd hdone
      have he' : μ.real {omega | ∀ n x,
          |f x - actualKernelMeanAt kernel lambda (fun i => query i omega) (fun y => f y) (fun i => Y i omega) n x| ≤
            actualSourceRadius kernel lambda B delta (fun i => query i omega) n x} = 1 := by
        change (μ _).toReal = 1
        rw [he, ENNReal.toReal_one]
      rw [he']
      linarith

variable [PseudoMetricSpace X]

/-- The exact GP raw bands and the literal seed-initialized intersection
and expansion recursion protect every point of every computed safe round
on the common confidence event. The query membership premise is the
algorithm's computed-set selection rule, not a safety conclusion. -/
theorem actual_source_beta_initialized_safeopt_learning_queries_are_safe_with_one_joint_probability
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
    1 - delta ≤ μ.real {omega | (∀ n, threshold ≤ f (query n omega)) ∧
      ∀ n x, x ∈ actualInitializedSafeFinset seed threshold
        (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) constant n →
          threshold ≤ f x} := by
  have he := (actual_source_beta_posterior_confidence_includes_zero_noise μ F kernel hkernel query hq
    Y hY R hYb hz lambda hlambda hscale f B hB delta hd hdone).2
  apply he.trans
  apply measureReal_mono _ (measure_ne_top μ _)
  intro omega hw
  have hraw : ∀ j x, f x ∈ Icc
      (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega) (j + 1) x)
      (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega) (j + 1) x) := by
    intro j x
    have hh := abs_le.mp (hw j x)
    simp only [actualSourceRawLower, actualSourceRawUpper, Nat.add_sub_cancel]
    exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have hsafe := (actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
    (fun x => f x) constant hf threshold seed hseed_nonempty hseed
      (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega))
      (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega)) hraw).2.2.2.2
  exact ⟨fun n => hsafe n (query n omega) (hquery omega n), hsafe⟩

end SafeLearning.CompleteModulesLandscapeSuiSafeOptSafety
