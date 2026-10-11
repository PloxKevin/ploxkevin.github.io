import SafeLearning.CompleteModulesLandscapeVisitConsistency

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVisitSquareRoot
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteModulesLandscapePredictableNoise
open CompleteModulesLandscapeQueryNoise CompleteModulesLandscapeVisitProcess
open CompleteModulesLandscapeVisitConfidence CompleteFoundationsTelescopingModels

/-- This is ordinary positive-variance algebra, not random optimization of a tilt. -/
theorem actual_positive_variance_optimized_exponential_boundary_equals_the_square_root
    (variance logarithm : ℝ) (hv : 0 < variance) (hL : 0 < logarithm) :
    logarithm / Real.sqrt (2 * logarithm / variance) +
      Real.sqrt (2 * logarithm / variance) * variance / 2 =
        Real.sqrt (2 * variance * logarithm) := by
  have hx : 0 < Real.sqrt (2 * logarithm / variance) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * logarithm / variance) ^ 2 = 2 * logarithm / variance :=
    Real.sq_sqrt (by positivity)
  have hsqv : Real.sqrt (2 * logarithm / variance) ^ 2 * variance = 2 * logarithm := by
    rw [hsq]
    field_simp
  have hratio : logarithm / Real.sqrt (2 * logarithm / variance) =
      Real.sqrt (2 * logarithm / variance) * variance / 2 := by
    apply (div_eq_iff hx.ne').2
    nlinarith [hsqv]
  have he : Real.sqrt (2 * logarithm / variance) * variance =
      Real.sqrt (2 * variance * logarithm) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [hsqv]
  rw [hratio]
  nlinarith

/-- Each tilt is fixed before the experiment. Summable budgets cover them all,
so choosing an integer count afterwards uses an already simultaneous event. -/
theorem actual_arbitrary_positive_fixed_tilts_share_one_all_design_all_time_event
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta)
    (tilts : ℕ → ℝ) (htilts : ∀ m, 0 < tilts m) :
    1 - delta ≤ μ.real {omega | ∀ m x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R (tilts m) (failureShare delta m / Fintype.card D) n omega} := by
  let bad : ℕ → Set Ω := fun m => {omega | ∃ x n,
    visitBoundary query x R (tilts m) (failureShare delta m / Fintype.card D) n omega ≤
      |collectedNoise query Y x n omega|}
  have hm : ∀ m, MeasurableSet (bad m) := by
    intro m
    have heq : bad m = ⋃ x, ⋃ n, {omega |
        visitBoundary query x R (tilts m) (failureShare delta m / Fintype.card D) n omega ≤
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
    have hq := (actual_adaptive_query_selection_weights_are_predictable F query hquery x).1
    have hqn : ∀ i, StronglyMeasurable[F (i + 1)] (queryWeight query x i) :=
      fun i => (hq i).mono (F.mono (Nat.le_succ i))
    have hcount : Measurable (visitCount query x n) :=
      ((partialSum_adapted F _ hqn n).mono (F.le n)).measurable
    exact measurableSet_le
      (measurable_const.add ((measurable_const.mul hcount).div_const 2))
      (((partialSum_adapted F _ hp.1 n).measurable.mono (F.le n) le_rfl).norm)
  have hp : ∀ m, μ.real (bad m) ≤ failureShare delta m := by
    intro m
    exact actual_any_finite_design_visit_count_boundary_crossing_probability
      μ F query hquery Y hY R hb hz (tilts m) (failureShare delta m)
      (htilts m) (by unfold failureShare; positivity)
  have h := actual_one_event_covering_every_round_has_the_true_probability_guarantee
    μ bad delta hd.le hm hp
  have heq : {omega | ∀ m x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R (tilts m) (failureShare delta m / Fintype.card D) n omega} =
      ⋂ m, (bad m)ᶜ := by
    ext omega
    simp [bad,not_le]
  rwa [heq]

/-- The logarithmic budget for count m is genuinely positive on delta in(0,1). -/
theorem actual_positive_failure_share_gives_a_positive_square_root_logarithm
    {D : Type*} [Fintype D] [Nonempty D] (delta : ℝ) (hd : 0 < delta)
    (hdone : delta < 1) (m : ℕ) :
    0 < Real.log (2 / (failureShare delta m / Fintype.card D)) := by
  have hc : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hcp : (0 : ℝ) < Fintype.card D := by positivity
  have hden : 1 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hdp : 0 < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
  have hs : 0 < failureShare delta m / Fintype.card D := by unfold failureShare; positivity
  have hshare : failureShare delta m ≤ delta := by
    unfold failureShare
    apply (div_le_iff₀ hdp).2
    nlinarith
  have hb : failureShare delta m / Fintype.card D < 2 := by
    apply (div_lt_iff₀ hcp).2
    linarith
  apply Real.log_pos
  apply (lt_div_iff₀ hs).2
  simpa using hb

/-- A true square-root count boundary holds jointly at every positive actual
visit count. The count is its exact selected-index cardinality; no random tilt
is put inside a pre-existing martingale theorem. -/
theorem actual_all_time_all_design_collected_noise_has_a_square_root_actual_count_bound
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hR : 0 < R) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) (hdone : delta < 1) :
    1 - delta ≤ μ.real {omega | ∀ x n, 0 < visitCount query x n omega →
      |collectedNoise query Y x n omega| < Real.sqrt
        (2 * ((R : ℝ) ^ 2 * visitCount query x n omega) *
          Real.log (2 / (failureShare delta
            (((Finset.range n).filter (fun i => query i omega = x)).card) / Fintype.card D)))} := by
  let logarithm : ℕ → ℝ := fun m => Real.log (2 / (failureShare delta m / Fintype.card D))
  let tilts : ℕ → ℝ := fun m => if m = 0 then 1 else
    Real.sqrt (2 * logarithm m / ((R : ℝ) ^ 2 * m))
  have hL : ∀ m, 0 < logarithm m :=
    actual_positive_failure_share_gives_a_positive_square_root_logarithm delta hd hdone
  have hRp : (0 : ℝ) < R := NNReal.coe_pos.2 hR
  have htilts : ∀ m, 0 < tilts m := by
    intro m
    by_cases hm : m = 0
    · simp [tilts,hm]
    · simp only [tilts,ite_eq_right hm]
      have hmp : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hLm := hL m
      exact Real.sqrt_pos.2 (by positivity)
  have hevent := actual_arbitrary_positive_fixed_tilts_share_one_all_design_all_time_event
    μ F query hquery Y hY R hb hz delta hd tilts htilts
  apply hevent.trans
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro omega homega x n hcount
  let m : ℕ := ((Finset.range n).filter (fun i => query i omega = x)).card
  have hcount_eq : visitCount query x n omega = (m : ℝ) :=
    (actual_visit_count_is_the_real_cardinality_of_the_selected_indices query x n omega).1
  have hmp : (0 : ℝ) < m := by rwa [hcount_eq] at hcount
  have hm : m ≠ 0 := by exact_mod_cast hmp.ne'
  have hv : 0 < (R : ℝ) ^ 2 * m := by positivity
  have hbound := homega m x n
  unfold visitBoundary at hbound
  rw [hcount_eq] at hbound
  change |collectedNoise query Y x n omega| <
    logarithm m / tilts m + tilts m * (R : ℝ) ^ 2 * m / 2 at hbound
  simp only [tilts,ite_eq_right hm] at hbound
  have heq := actual_positive_variance_optimized_exponential_boundary_equals_the_square_root
    ((R : ℝ) ^ 2 * m) (logarithm m) hv (hL m)
  rw [mul_assoc] at hbound
  rw [heq] at hbound
  simpa only [hcount_eq,logarithm,m] using hbound

end SafeLearning.CompleteModulesLandscapeVisitSquareRoot
