import SafeLearning.CompleteModulesLandscapeSuiSafeOptProbability
import SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteModulesLandscapeSuiSafeOptSafety CompleteModulesLandscapeSuiSafeOptProbability
open CompleteModulesLandscapeSafeOptMeasurable CompleteModulesLandscapeSafeOptQueryProtocol
open CompleteModulesSafeOptFiniteOptimality CompleteModulesSafeOptInitializedRun

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]

/-- The literal finite width-maximizing rule needs well-formed endpoints only
on the actual good confidence event. Truth of the raw bands derives both
nonemptiness and ordering there, before the actual selector is invoked. -/
theorem actual_initialized_width_maximizing_protocol_is_safe_on_true_raw_bands
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
  have hbands := (actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
    f seed threshold rawLower rawUpper hraw hseed).1
  have hrun := actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
    f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw
  have hsafe := hrun.2.2.2.2
  refine ⟨?_,hsafe⟩
  intro n
  have hs := hrun.1 n
  have hb : ∀ x ∈ actualInitializedSafeFinset seed threshold rawLower constant n,
      actualContainedLower seed threshold rawLower n x ≤ actualContainedUpper rawUpper n x :=
    fun x _ => (hbands n x).1.trans (hbands n x).2
  apply hsafe n
  rw [hprotocol n hs hb]
  exact actual_initialized_contained_band_width_maximizer_is_in_the_computed_safe_finset
    seed threshold rawLower rawUpper constant n hs hb

variable {H : Type*} [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- The exact source beta protects the literal width-maximizing algorithm
on one measurable event, without global ordered-band assumptions. -/
theorem actual_source_beta_width_maximizing_safeopt_has_one_measurable_alltime_safety_event
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
  constructor
  · exact actual_initialized_query_and_every_safe_round_safety_event_is_measurable
      (fun x => f x) seed threshold constant
      (fun omega => actualSourceRawLower kernel lambda B delta
        (fun i => query i omega) (fun x => f x) (fun i => Y i omega))
      (fun n x => actual_source_beta_raw_lower_endpoint_is_measurable
        F kernel lambda B delta query hq Y hY (fun x => f x) n x)
      query (fun i => (hq i).mono (F.le i) le_rfl)
  · have he := (actual_source_beta_posterior_confidence_includes_zero_noise
      μ F kernel hkernel query hq Y hY R hYb hz lambda hlambda hscale f B hB delta hd hdone).2
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
    exact actual_initialized_width_maximizing_protocol_is_safe_on_true_raw_bands
      (fun x => f x) constant hf threshold seed hseed_nonempty hseed
      (actualSourceRawLower kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega))
      (actualSourceRawUpper kernel lambda B delta (fun i => query i omega) (fun x => f x) (fun i => Y i omega))
      hraw (fun n => query n omega) (fun n hs hb => hprotocol omega n hs hb)

/-- The literal all-time query-safety probability follows on that same event. -/
theorem actual_source_beta_width_maximizing_safeopt_alltime_query_safety_probability
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
  constructor
  · have heq : {omega | ∀ n, threshold ≤ f (query n omega)} =
        ⋂ n, {omega | threshold ≤ f (query n omega)} := by ext omega; simp
    rw [heq]
    exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const
      ((measurable_of_countable (fun x => f x)).comp ((hq n).mono (F.le n) le_rfl)))
  · apply (actual_source_beta_width_maximizing_safeopt_has_one_measurable_alltime_safety_event
      μ F kernel hkernel query hq Y hY R hYb hz lambda hlambda hscale f B hB delta hd hdone
      constant hf threshold seed hseed_nonempty hseed hprotocol).2.trans
    exact measureReal_mono (fun _ hw => hw.1) (measure_ne_top μ _)

end SafeLearning.CompleteModulesLandscapeSuiSafeOptAlgorithm
