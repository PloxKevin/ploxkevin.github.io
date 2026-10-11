import SafeLearning.CompleteModulesLandscapeVisitConfidence
import SafeLearning.CompleteFoundationsTelescopingModels

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVisitConsistency
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteModulesLandscapePredictableNoise
open CompleteModulesLandscapeQueryNoise CompleteModulesLandscapeVisitProcess
open CompleteModulesLandscapeVisitConfidence CompleteFoundationsTelescopingModels

def tilt (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

/-- A count tending to infinity and confidence slopes tending to zero give
true convergence of the averaged sum. No independence or pre-assumed limit is used. -/
theorem actual_all_tilt_average_bounds_and_infinite_visit_count_imply_zero_limit
    (sum count : ℕ → ℝ) (R : ℝ≥0) (C : ℕ → ℝ)
    (hcount : Tendsto count atTop atTop)
    (hbound : ∀ j n, 0 < count n →
      |sum n / count n| ≤ C j / count n + tilt j * (R : ℝ) ^ 2 / 2) :
    Tendsto (fun n => sum n / count n) atTop (𝓝 0) := by
  have htilt : Tendsto tilt atTop (𝓝 0) := by
    simpa only [tilt,one_div,Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun j => tilt j * (R : ℝ) ^ 2 / 2) atTop (𝓝 0) := by
    simpa using (htilt.mul_const ((R : ℝ) ^ 2)).div_const 2
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨j,hj⟩ := (hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))).exists
  have hfirst : Tendsto (fun n => C j / count n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Pi.inv_apply,mul_zero] using hcount.inv_tendsto_atTop.const_mul (C j)
  have he : ∀ᶠ n in atTop, C j / count n < epsilon / 2 :=
    hfirst.eventually (gt_mem_nhds (by positivity))
  have hp : ∀ᶠ n in atTop, 0 < count n := hcount.eventually (eventually_gt_atTop 0)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and hp)
  refine ⟨N,?_⟩
  intro n hn
  have h := hbound j n (hN n hn).2
  rw [Real.dist_eq,sub_zero]
  linarith [(hN n hn).1]

/-- A genuinely summable failure allocation combines all fixed tilts without
independence, so every point and every time share the same event. -/
theorem actual_all_finite_design_all_time_all_tilt_visit_confidence_event
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ j x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R (tilt j) (failureShare delta j / Fintype.card D) n omega} := by
  let bad : ℕ → Set Ω := fun j => {omega | ∃ x n,
    visitBoundary query x R (tilt j) (failureShare delta j / Fintype.card D) n omega ≤
      |collectedNoise query Y x n omega|}
  have hm : ∀ j, MeasurableSet (bad j) := by
    intro j
    have heq : bad j = ⋃ x, ⋃ n, {omega |
        visitBoundary query x R (tilt j) (failureShare delta j / Fintype.card D) n omega ≤
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
  have hp : ∀ j, μ.real (bad j) ≤ failureShare delta j := by
    intro j
    exact actual_any_finite_design_visit_count_boundary_crossing_probability
      μ F query hquery Y hY R hb hz (tilt j) (failureShare delta j)
      (by unfold tilt; positivity) (by unfold failureShare; positivity)
  have h := actual_one_event_covering_every_round_has_the_true_probability_guarantee
    μ bad delta hd.le hm hp
  have heq : {omega | ∀ j x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R (tilt j) (failureShare delta j / Fintype.card D) n omega} =
      ⋂ j, (bad j)ᶜ := by
    ext omega
    simp [bad,not_le]
  rwa [heq]

/-- On an event of probability at least1-delta, every design point visited
infinitely often has its actual collected-noise average converge to zero. -/
theorem actual_adaptively_collected_noise_average_converges_when_visits_diverge
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (delta : ℝ) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ x, Tendsto (fun n => visitCount query x n omega) atTop atTop →
      Tendsto (fun n => collectedNoise query Y x n omega / visitCount query x n omega) atTop (𝓝 0)} := by
  have hevent := actual_all_finite_design_all_time_all_tilt_visit_confidence_event
    μ F query hquery Y hY R hb hz delta hd
  apply hevent.trans
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro omega homega x hcount
  apply actual_all_tilt_average_bounds_and_infinite_visit_count_imply_zero_limit
    (fun n => collectedNoise query Y x n omega) (fun n => visitCount query x n omega) R
    (fun j => Real.log (2 / (failureShare delta j / Fintype.card D)) / tilt j) hcount
  intro j n hp
  have h := (div_lt_div_iff_of_pos_right hp).mpr (homega j x n)
  rw [abs_div,abs_of_pos hp]
  have heq : visitBoundary query x R (tilt j) (failureShare delta j / Fintype.card D) n omega /
      visitCount query x n omega =
      Real.log (2 / (failureShare delta j / Fintype.card D)) / tilt j / visitCount query x n omega +
        tilt j * (R : ℝ) ^ 2 / 2 := by
    unfold visitBoundary
    field_simp
    <;> ring
  rw [heq] at h
  exact h.le

end SafeLearning.CompleteModulesLandscapeVisitConsistency
