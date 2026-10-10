import SafeLearning.CompleteModulesLandscapePredictableNoise

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeQueryNoise
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteModulesLandscapeScalarConfidence
open CompleteModulesLandscapePredictableNoise

def collectedNoise {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D)
    (Y : ℕ → Ω → ℝ) (x : D) : ℕ → Ω → ℝ :=
  partialSum (fun i => queryWeight query x i * Y i)

/-- The noise actually collected at each adaptively selected design point has
the conditional law derived from the original noise hypotheses. -/
theorem actual_query_filtered_increments_have_the_derived_conditional_noise_law
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D) :
    (∀ i, StronglyMeasurable[F (i + 1)] (queryWeight query x i * Y i)) ∧
      (∀ i, RealConditionalSubGaussian μ (F i) (F.le i)
        (queryWeight query x i * Y i) (R ^ 2)) := by
  have hp := actual_adaptive_query_selection_weights_are_predictable F query hquery x
  have hw := actual_predictable_weighted_noise_has_the_derived_conditional_law
    μ F (queryWeight query x) Y hp.1 hY 1 R
    (fun i => Eventually.of_forall (hp.2 i)) hb hz
  simpa only [one_mul] using hw

/-- An all-time bound for each actual collected-noise sum, without independent queries. -/
theorem actual_each_design_collected_noise_all_time_crossing_probability
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (x : D) (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    μ.real {omega | ∃ n, linearBoundary R lambda delta n ≤ |collectedNoise query Y x n omega|} ≤ delta := by
  have hp := actual_query_filtered_increments_have_the_derived_conditional_noise_law
    μ F query hquery Y hY R hb hz x
  exact actual_all_time_absolute_noise_sum_crossing_probability μ F
    (fun i => queryWeight query x i * Y i) hp.1 R hp.2 lambda delta hl hd

/-- A true finite-design union bound combines the actual all-time events. -/
theorem actual_any_finite_design_collected_noise_crossing_probability
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    μ.real {omega | ∃ x n, linearBoundary R lambda (delta / Fintype.card D) n ≤
      |collectedNoise query Y x n omega|} ≤ delta := by
  have hc : 0 < (Fintype.card D : ℝ) := by exact_mod_cast Fintype.card_pos
  let bad : D → Set Ω := fun x => {omega | ∃ n,
    linearBoundary R lambda (delta / Fintype.card D) n ≤ |collectedNoise query Y x n omega|}
  have heq : {omega | ∃ x n, linearBoundary R lambda (delta / Fintype.card D) n ≤
      |collectedNoise query Y x n omega|} = ⋃ x, bad x := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, bad]
  rw [heq]
  calc
    μ.real (⋃ x, bad x) ≤ ∑ x, μ.real (bad x) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _x : D, delta / Fintype.card D := by
      apply Finset.sum_le_sum
      intro x hx
      exact actual_each_design_collected_noise_all_time_crossing_probability
        μ F query hquery Y hY R hb hz x lambda (delta / Fintype.card D) hl (div_pos hd hc)
    _ = delta := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

/-- The joint event is measurable and holds for every design point and every time. -/
theorem actual_finite_design_all_point_all_time_collected_noise_confidence_event
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ x n, |collectedNoise query Y x n omega| <
      linearBoundary R lambda (delta / Fintype.card D) n} := by
  let bad : Set Ω := {omega | ∃ x n, linearBoundary R lambda (delta / Fintype.card D) n ≤
    |collectedNoise query Y x n omega|}
  have hm : MeasurableSet bad := by
    have heq : bad = ⋃ x, ⋃ n, {omega | linearBoundary R lambda (delta / Fintype.card D) n ≤
      |collectedNoise query Y x n omega|} := by
      ext omega
      simp [bad]
    rw [heq]
    apply MeasurableSet.iUnion
    intro x
    apply MeasurableSet.iUnion
    intro n
    have hp := actual_query_filtered_increments_have_the_derived_conditional_noise_law
      μ F query hquery Y hY R hb hz x
    exact measurableSet_le measurable_const
      (((partialSum_adapted F _ hp.1 n).measurable.mono (F.le n) le_rfl).norm)
  have heq : {omega | ∀ x n, |collectedNoise query Y x n omega| <
      linearBoundary R lambda (delta / Fintype.card D) n} = badᶜ := by
    ext omega
    simp [bad, not_le]
  have hh := actual_any_finite_design_collected_noise_crossing_probability
    μ F query hquery Y hY R hb hz lambda delta hl hd
  rw [heq, measureReal_compl hm, probReal_univ]
  change μ.real bad ≤ delta at hh
  linarith

end SafeLearning.CompleteModulesLandscapeQueryNoise
