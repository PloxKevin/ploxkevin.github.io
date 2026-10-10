import SafeLearning.CompleteModulesLandscapeVisitConsistency
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVisitAlmostSure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteAppliedAzuma CompleteModulesLandscapePredictableNoise
open CompleteModulesLandscapeQueryNoise CompleteModulesLandscapeVisitProcess
open CompleteModulesLandscapeVisitConsistency

/-- The actual adaptive-query count and noise-average limit implication is
a measurable event. Zero-count divisions are totalized only before the limit. -/
theorem actual_infinite_visit_noise_average_limit_event_is_measurable
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D]
    (F : Filtration ℕ mΩ) (query : ℕ → Ω → D)
    (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) :
    MeasurableSet {omega | ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} := by
  have hx : ∀ x : D, MeasurableSet {omega |
      Tendsto (fun n => visitCount query x n omega) atTop atTop →
        Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} := by
    intro x
    have hq := (actual_adaptive_query_selection_weights_are_predictable F query hquery x).1
    have hqn : ∀ i, StronglyMeasurable[F (i + 1)] (queryWeight query x i) :=
      fun i => (hq i).mono (F.mono (Nat.le_succ i))
    have hcount : ∀ n, Measurable (visitCount query x n) :=
      fun n => ((partialSum_adapted F _ hqn n).mono (F.le n)).measurable
    have hprod : ∀ i, StronglyMeasurable[F (i + 1)] (queryWeight query x i * Y i) :=
      fun i => (hqn i).mul (hY i)
    have hsum : ∀ n, Measurable (collectedNoise query Y x n) :=
      fun n => ((partialSum_adapted F _ hprod n).mono (F.le n)).measurable
    have ha := measurableSet_tendsto (atTop : Filter ℝ) hcount
    have hb := measurableSet_tendsto (𝓝 (0 : ℝ)) (fun n => (hsum n).div (hcount n))
    have heq : {omega | Tendsto (fun n => visitCount query x n omega) atTop atTop →
        Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} =
        {omega | Tendsto (fun n => visitCount query x n omega) atTop atTop}ᶜ ∪
          {omega | Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} := by
      ext omega
      simp [imp_iff_not_or]
    rw [heq]
    exact ha.compl.union hb
  have heq : {omega | ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} =
      ⋂ x : D, {omega | Tendsto (fun n => visitCount query x n omega) atTop atTop →
        Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} := by
    ext omega
    simp
  rw [heq]
  exact MeasurableSet.iInter hx

/-- Every positive failure budget controls this same actual limit event,
so its genuine probability equals one. -/
theorem actual_adaptive_infinite_visit_noise_average_limit_has_probability_one
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) :
    μ.real {omega | ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} = 1 := by
  apply le_antisymm
  · exact (measureReal_mono (subset_univ _) (measure_ne_top μ univ)).trans_eq probReal_univ
  · apply le_of_forall_pos_le_add
    intro delta hd
    have h := actual_adaptively_collected_noise_average_converges_when_visits_diverge
      μ F query hquery Y hY R hb hz delta hd
    linarith

/-- Actual collected noise is strongly consistent at every infinitely visited
point almost surely, without independent increments or independent queries. -/
theorem actual_bounded_given_past_noise_is_almost_surely_consistent_at_infinitely_visited_points
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) :
    ∀ᵐ omega ∂μ, ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0) := by
  have hm := actual_infinite_visit_noise_average_limit_event_is_measurable F query hquery Y hY
  have hp := actual_adaptive_infinite_visit_noise_average_limit_has_probability_one
    μ F query hquery Y hY R hb hz
  rw [ae_iff]
  apply (measureReal_eq_zero_iff (measure_ne_top μ _)).mp
  have heq : {omega | ¬ (∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0))} =
      {omega | ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
        Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)}ᶜ := rfl
  rw [heq,probReal_compl_eq_one_sub hm,hp]
  norm_num

end SafeLearning.CompleteModulesLandscapeVisitAlmostSure
