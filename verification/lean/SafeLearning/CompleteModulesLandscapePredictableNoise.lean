import SafeLearning.CompleteModulesLandscapeScalarConfidence

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapePredictableNoise
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteAppliedAzuma CompleteModulesLandscapeScalarConfidence

/-- Past-measurable bounded weights preserve actual conditional centering. -/
theorem actual_bounded_predictable_weight_preserves_conditional_zero_and_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (q Y : Ω → ℝ) (hq : StronglyMeasurable[m] q)
    (hY : @Measurable Ω ℝ mΩ inferInstance Y)
    (K R : ℝ≥0) (hqbound : ∀ᵐ omega ∂μ, |q omega| ≤ K)
    (hYbound : ∀ᵐ omega ∂μ, Y omega ∈ Icc (-(R : ℝ)) R)
    (hzero : μ[Y | m] =ᵐ[μ] 0) :
    μ[q * Y | m] =ᵐ[μ] 0 ∧
      (∀ᵐ omega ∂μ, (q * Y) omega ∈ Icc (-((K * R : ℝ≥0) : ℝ)) (K * R : ℝ≥0)) := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable Y μ :=
    (memLp_of_bounded hYbound hY.aestronglyMeasurable 2).integrable (by norm_num)
  have hqnorm : ∀ᵐ omega ∂μ, ‖q omega‖ ≤ (K : ℝ) := by
    simpa only [Real.norm_eq_abs] using hqbound
  have hp := condExp_stronglyMeasurable_mul_of_bound hm hq hi (K : ℝ) hqnorm
  constructor
  · filter_upwards [hp, hzero] with omega hp hzero
    simpa only [Pi.mul_apply, Pi.zero_apply, hzero, mul_zero] using hp
  · filter_upwards [hqbound, hYbound] with omega hqbound hYbound
    have ha : |Y omega| ≤ (R : ℝ) := abs_le.mpr hYbound
    have hb : |q omega * Y omega| ≤ (K : ℝ) * (R : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hqbound ha (abs_nonneg _) K.property
    simpa only [Pi.mul_apply, NNReal.coe_mul, Set.mem_Icc] using abs_le.mp hb

/-- The product is adapted at the next stage and has the true conditional MGF bound. -/
theorem actual_predictable_weighted_noise_has_the_derived_conditional_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ)
    (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (K R : ℝ≥0) (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) :
    (∀ i, StronglyMeasurable[F (i + 1)] (q i * Y i)) ∧
      (∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (q i * Y i) ((K * R) ^ 2)) := by
  have hprod (i : ℕ) : StronglyMeasurable[F (i + 1)] (q i * Y i) :=
    ((hq i).mono (F.mono (Nat.le_succ i))).mul (hY i)
  refine ⟨hprod, ?_⟩
  intro i
  have hpair := actual_bounded_predictable_weight_preserves_conditional_zero_and_support
    μ (F i) (F.le i) (q i) (Y i) (hq i)
    ((hY i).mono (F.le (i + 1))).measurable K R (hqbound i) (hYbound i) (hzero i)
  exact bounded_centered_is_real_conditional_subgaussian μ (F i) (F.le i) (q i * Y i)
    ((hprod i).mono (F.le (i + 1))).measurable (K * R) hpair.2 hpair.1

/-- Uniformly bounded arbitrary predictable weights give an actual simultaneous event. -/
theorem actual_predictable_weighted_noise_has_the_all_time_linear_confidence_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ)
    (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (K R : ℝ≥0) (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n,
      |partialSum (fun i => q i * Y i) n omega| < linearBoundary (K * R) lambda delta n} := by
  have hp := actual_predictable_weighted_noise_has_the_derived_conditional_law
    μ F q Y hq hY K R hqbound hYbound hzero
  exact actual_simultaneous_noise_sum_linear_confidence_event μ F
    (fun i => q i * Y i) hp.1 (K * R) hp.2 lambda delta hl hd

def queryWeight {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D)
    (x : D) (i : ℕ) (omega : Ω) : ℝ := if query i omega = x then 1 else 0

/-- Actual adaptive queries determine past-measurable, bounded selection weights. -/
theorem actual_adaptive_query_selection_weights_are_predictable
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (F : Filtration ℕ mΩ) (query : ℕ → Ω → D)
    (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i)) (x : D) :
    (∀ i, StronglyMeasurable[F i] (queryWeight query x i)) ∧
      (∀ i omega, |queryWeight query x i omega| ≤ (1 : ℝ)) := by
  constructor
  · intro i
    have hs : MeasurableSet[F i] {omega | query i omega = x} := by
      exact hquery i (measurableSet_singleton x)
    exact (measurable_const.ite hs measurable_const).stronglyMeasurable
  · intro i omega
    unfold queryWeight
    split_ifs <;> norm_num

/-- The actual filtered sum is exactly the noise collected at this design point. -/
theorem actual_query_filtered_partial_sum_is_the_observed_noise_sum
    {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D) (Y : ℕ → Ω → ℝ)
    (x : D) (n : ℕ) (omega : Ω) :
    partialSum (fun i => queryWeight query x i * Y i) n omega =
      ∑ i ∈ Finset.range n, if query i omega = x then Y i omega else 0 := by
  simp only [partialSum, Pi.mul_apply, queryWeight]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

end SafeLearning.CompleteModulesLandscapePredictableNoise
