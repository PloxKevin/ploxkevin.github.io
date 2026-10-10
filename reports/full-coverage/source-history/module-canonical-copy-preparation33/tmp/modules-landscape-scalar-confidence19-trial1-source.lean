import SafeLearning.CompleteAppliedExponentialMartingale
import SafeLearning.CompleteAppliedStopping

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeScalarConfidence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale CompleteAppliedStopping

/-- Actual Ville composition for the exponential process of an adapted noise sum. -/
theorem actual_all_time_noise_sum_exponential_boundary_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda delta : ℝ) (hd : 0 < delta) :
    μ.real {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum Y n omega - lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2} ≤ delta := by
  have heq : {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum Y n omega - lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2} =
      {omega | ∃ n, 1 / delta ≤ exponentialProcess Y R lambda n omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, exponentialProcess]
    congr 1
    ext n
    rw [← Real.exp_le_exp, Real.exp_log (by positivity : 0 < 1 / delta)]
  rw [heq]
  have hv := ville μ F (exponentialProcess Y R lambda)
    (actual_exponential_supermartingale μ F Y hY R hcond lambda)
    (fun n => Eventually.of_forall fun omega =>
      (exponential_initial_positive Y R lambda).2 n omega |>.le)
    (1 / delta) (by positivity)
  have hi : (∫ omega, exponentialProcess Y R lambda 0 omega ∂μ) = 1 := by
    rw [(exponential_initial_positive Y R lambda).1]
    simp
  rw [hi] at hv
  simpa using hv

def linearBoundary (R : ℝ≥0) (lambda delta : ℝ) (n : ℕ) : ℝ :=
  Real.log (2 / delta) / lambda + lambda * (R : ℝ) ^ 2 * (n : ℝ) / 2

/-- One fixed positive slope gives a true simultaneous two-sided linear boundary. -/
theorem actual_all_time_absolute_noise_sum_crossing_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    μ.real {omega | ∃ n, linearBoundary R lambda delta n ≤ |partialSum Y n omega|} ≤ delta := by
  let A : Set Ω := {omega | ∃ n, Real.log (1 / (delta / 2)) ≤
    lambda * partialSum Y n omega - lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2}
  let B : Set Ω := {omega | ∃ n, Real.log (1 / (delta / 2)) ≤
    (-lambda) * partialSum Y n omega - (-lambda) ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2}
  have hsubset : {omega | ∃ n, linearBoundary R lambda delta n ≤ |partialSum Y n omega|} ⊆ A ∪ B := by
    intro omega homega
    obtain ⟨n, hn⟩ := homega
    have hprod := mul_le_mul_of_nonneg_left hn hl.le
    have hm : lambda * linearBoundary R lambda delta n =
        Real.log (2 / delta) + lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2 := by
      unfold linearBoundary
      field_simp
      <;> ring
    rw [hm] at hprod
    have hlog : Real.log (1 / (delta / 2)) = Real.log (2 / delta) := by
      congr 1
      field_simp
    by_cases hs : 0 ≤ partialSum Y n omega
    · rw [abs_of_nonneg hs] at hprod
      left
      exact ⟨n, by rw [hlog]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge hs)] at hprod
      right
      exact ⟨n, by rw [hlog]; dsimp; nlinarith [sq_nonneg lambda]⟩
  have ha := actual_all_time_noise_sum_exponential_boundary_probability μ F Y hY R hcond
    lambda (delta / 2) (by positivity)
  have hb := actual_all_time_noise_sum_exponential_boundary_probability μ F Y hY R hcond
    (-lambda) (delta / 2) (by positivity)
  calc
    _ ≤ μ.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ delta := by dsimp only [A, B] at *; linarith

/-- The simultaneous event is measurable and has the actual stated probability. -/
theorem actual_simultaneous_noise_sum_linear_confidence_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n, |partialSum Y n omega| < linearBoundary R lambda delta n} := by
  let bad : Set Ω := {omega | ∃ n, linearBoundary R lambda delta n ≤ |partialSum Y n omega|}
  have hbad : MeasurableSet bad := by
    have heq : bad = ⋃ n, {omega | linearBoundary R lambda delta n ≤ |partialSum Y n omega|} := by
      ext omega
      simp [bad]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_le measurable_const
      (((partialSum_adapted F Y hY n).measurable.mono (F.le n) le_rfl).norm)
  have hbound := actual_all_time_absolute_noise_sum_crossing_probability μ F Y hY R hcond lambda delta hl hd
  have heq : {omega | ∀ n, |partialSum Y n omega| < linearBoundary R lambda delta n} = badᶜ := by
    ext omega
    simp [bad, not_le]
  rw [heq, measureReal_compl hbad, probReal_univ]
  change μ.real bad ≤ delta at hbound
  linarith

/-- Bounded actual conditional-zero noise instantiates the simultaneous bound directly. -/
theorem actual_bounded_given_past_noise_has_the_simultaneous_linear_confidence_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0)
    (lambda delta : ℝ) (hl : 0 < lambda) (hd : 0 < delta) :
    1 - delta ≤ μ.real {omega | ∀ n, |partialSum Y n omega| < linearBoundary R lambda delta n} := by
  apply actual_simultaneous_noise_sum_linear_confidence_event μ F Y hY R _ lambda delta hl hd
  intro i
  exact bounded_centered_is_real_conditional_subgaussian μ (F i) (F.le i) (Y i)
    ((hY i).mono (F.le (i + 1))).measurable R (hb i) (hz i)

end SafeLearning.CompleteModulesLandscapeScalarConfidence
