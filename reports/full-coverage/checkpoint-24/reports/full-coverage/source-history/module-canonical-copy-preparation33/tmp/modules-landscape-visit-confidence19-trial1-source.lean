import SafeLearning.CompleteModulesLandscapeVisitProcess
import SafeLearning.CompleteModulesLandscapeQueryNoise

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVisitConfidence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteModulesLandscapePredictableNoise
open CompleteModulesLandscapeQueryNoise CompleteModulesLandscapeVisitProcess

def visitBoundary {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D)
    (x : D) (R : ℝ≥0) (lambda delta : ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  Real.log (2 / delta) / lambda + lambda * (R : ℝ) ^ 2 * visitCount query x n omega / 2

/-- The two tails are combined with the actual adaptive visit count in both compensators. -/
theorem actual_all_time_absolute_collected_noise_visit_boundary_probability
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    μ.real {omega | ∃ n, visitBoundary query x R lambda delta n omega ≤
      |collectedNoise query Y x n omega|} ≤ delta := by
  let A : Set Ω := {omega | ∃ n, Real.log (1 / (delta / 2)) ≤
    lambda * collectedNoise query Y x n omega -
      lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2}
  let B : Set Ω := {omega | ∃ n, Real.log (1 / (delta / 2)) ≤
    (-lambda) * collectedNoise query Y x n omega -
      (-lambda) ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2}
  have hsubset : {omega | ∃ n, visitBoundary query x R lambda delta n omega ≤
      |collectedNoise query Y x n omega|} ⊆ A ∪ B := by
    rintro omega ⟨n,hn⟩
    have hp := mul_le_mul_of_nonneg_left hn hl.le
    have hm : lambda * visitBoundary query x R lambda delta n omega =
        Real.log (2 / delta) + lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2 := by
      unfold visitBoundary
      field_simp
      <;> ring
    rw [hm] at hp
    have hlog : Real.log (1 / (delta / 2)) = Real.log (2 / delta) := by
      congr 1
      field_simp
    by_cases hs : 0 ≤ collectedNoise query Y x n omega
    · rw [abs_of_nonneg hs] at hp
      left
      exact ⟨n,by rw [hlog]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge hs)] at hp
      right
      exact ⟨n,by rw [hlog]; nlinarith⟩
  have ha := actual_all_time_selected_noise_visit_count_boundary_probability
    μ F query hquery Y hY R hb hz x lambda (delta / 2) (by positivity)
  have hb' := actual_all_time_selected_noise_visit_count_boundary_probability
    μ F query hquery Y hY R hb hz x (-lambda) (delta / 2) (by positivity)
  calc
    _ ≤ μ.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ delta := by dsimp only [A,B,collectedNoise] at *; linarith

/-- One finite allocation gives a true simultaneous all-design, all-time probability bound. -/
theorem actual_any_finite_design_visit_count_boundary_crossing_probability
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    μ.real {omega | ∃ x n,
      visitBoundary query x R lambda (delta / Fintype.card D) n omega ≤
        |collectedNoise query Y x n omega|} ≤ delta := by
  have hc : 0 < (Fintype.card D : ℝ) := by exact_mod_cast Fintype.card_pos
  let bad : D → Set Ω := fun x => {omega | ∃ n,
    visitBoundary query x R lambda (delta / Fintype.card D) n omega ≤
      |collectedNoise query Y x n omega|}
  have heq : {omega | ∃ x n,
      visitBoundary query x R lambda (delta / Fintype.card D) n omega ≤
        |collectedNoise query Y x n omega|} = ⋃ x, bad x := by
    ext omega
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,bad]
  rw [heq]
  calc
    μ.real (⋃ x, bad x) ≤ ∑ x, μ.real (bad x) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _x : D, delta / Fintype.card D := by
      apply Finset.sum_le_sum
      intro x hx
      exact actual_all_time_absolute_collected_noise_visit_boundary_probability
        μ F query hquery Y hY R hb hz x lambda (delta / Fintype.card D) hl (div_pos hd hc)
    _ = delta := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp

/-- The actual simultaneous visit-based event is measurable and has probability at least1-delta. -/
theorem actual_all_design_all_time_visit_count_confidence_event
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R lambda (delta / Fintype.card D) n omega} := by
  let bad : Set Ω := {omega | ∃ x n,
    visitBoundary query x R lambda (delta / Fintype.card D) n omega ≤
      |collectedNoise query Y x n omega|}
  have hm : MeasurableSet bad := by
    have heq : bad = ⋃ x, ⋃ n, {omega |
        visitBoundary query x R lambda (delta / Fintype.card D) n omega ≤
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
    have hboundary : Measurable (visitBoundary query x R lambda (delta / Fintype.card D) n) :=
      measurable_const.add ((measurable_const.mul hcount).div_const 2)
    exact measurableSet_le hboundary
      (((partialSum_adapted F _ hp.1 n).measurable.mono (F.le n) le_rfl).norm)
  have heq : {omega | ∀ x n, |collectedNoise query Y x n omega| <
      visitBoundary query x R lambda (delta / Fintype.card D) n omega} = badᶜ := by
    ext omega
    simp [bad,not_le]
  have hh := actual_any_finite_design_visit_count_boundary_crossing_probability
    μ F query hquery Y hY R hb hz lambda delta hl hd
  rw [heq,measureReal_compl hm,probReal_univ]
  change μ.real bad ≤ delta at hh
  linarith

/-- Average collected noise is normalized only at points with a genuinely positive visit count. -/
theorem actual_all_design_all_time_positive_visit_noise_average_confidence
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D] [Fintype D] [Nonempty D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ x n, 0 < visitCount query x n omega →
      |collectedNoise query Y x n omega / visitCount query x n omega| <
        Real.log (2 / (delta / Fintype.card D)) / lambda / visitCount query x n omega +
          lambda * (R : ℝ) ^ 2 / 2} := by
  have hevent := actual_all_design_all_time_visit_count_confidence_event
    μ F query hquery Y hY R hb hz lambda delta hl hd
  apply hevent.trans
  apply measureReal_mono
  intro omega homega x n hcount
  have h := (div_lt_div_iff_of_pos_right hcount).mpr (homega x n)
  rw [abs_div,abs_of_pos hcount]
  have heq : visitBoundary query x R lambda (delta / Fintype.card D) n omega /
      visitCount query x n omega =
      Real.log (2 / (delta / Fintype.card D)) / lambda / visitCount query x n omega +
        lambda * (R : ℝ) ^ 2 / 2 := by
    unfold visitBoundary
    field_simp
    <;> ring
  rwa [heq] at h

end SafeLearning.CompleteModulesLandscapeVisitConfidence
