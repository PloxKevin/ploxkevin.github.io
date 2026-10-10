import SafeLearning.CompleteModulesLandscapePredictableNoise
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeVisitProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale CompleteAppliedStopping
open CompleteModulesLandscapePredictableNoise

def visitCount {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D)
    (x : D) : ℕ → Ω → ℝ := partialSum (queryWeight query x)

def visitProcess {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D)
    (Y : ℕ → Ω → ℝ) (x : D) (R : ℝ≥0) (lambda : ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  Real.exp (lambda * partialSum (fun i => queryWeight query x i * Y i) n omega -
    lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2)

/-- The compensator is the actual count of visits, not the total time. -/
theorem actual_visit_count_is_the_real_cardinality_of_the_selected_indices
    {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D) (x : D) (n : ℕ) (omega : Ω) :
    visitCount query x n omega =
      (((Finset.range n).filter (fun i => query i omega = x)).card : ℝ) ∧
      0 ≤ visitCount query x n omega := by
  constructor
  · simp [visitCount, partialSum, queryWeight, Finset.sum_boole]
  · unfold visitCount partialSum
    apply Finset.sum_nonneg
    intro i hi
    unfold queryWeight
    split_ifs <;> norm_num

/-- Conditioning on the past retains the zero cost for an unvisited point.
The actual increment MGF is bounded by the random predictable visit compensator. -/
theorem actual_selected_noise_conditional_mgf_uses_its_actual_visit_indicator
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D) (lambda : ℝ) (i : ℕ) :
    Integrable (fun omega => Real.exp (lambda * (queryWeight query x i * Y i) omega)) μ ∧
      ∀ᵐ omega ∂μ,
        (μ[fun w => Real.exp (lambda * (queryWeight query x i * Y i) w) | F i]) omega ≤
          Real.exp (lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x i omega / 2) := by
  let s : Set Ω := {omega | query i omega = x}
  have hs : MeasurableSet[F i] s := hquery i (measurableSet_singleton x)
  have hsΩ := (F.le i) _ hs
  have hc := bounded_centered_is_real_conditional_subgaussian μ (F i) (F.le i) (Y i)
    ((hY i).mono (F.le (i + 1))).measurable R (hb i) (hz i)
  have hm := actual_conditional_mgf μ (F i) (F.le i) (Y i)
    ((hY i).mono (F.le (i + 1))).measurable (R ^ 2) hc lambda
  let e : Ω → ℝ := fun omega => Real.exp (lambda * Y i omega)
  have heq : (fun omega => Real.exp (lambda * (queryWeight query x i * Y i) omega)) =
      s.indicator e + sᶜ.indicator (fun _ => (1 : ℝ)) := by
    ext omega
    by_cases h : query i omega = x <;> simp [s,e,queryWeight,h]
  have hi := (hm.1.indicator hsΩ).add ((integrable_const (1 : ℝ)).indicator hsΩ.compl)
  refine ⟨by rw [heq]; exact hi, ?_⟩
  have ha := condExp_add (hm.1.indicator hsΩ)
    ((integrable_const (1 : ℝ)).indicator hsΩ.compl) (F i)
  have hce := condExp_indicator hm.1 hs
  have hco := condExp_indicator (integrable_const (1 : ℝ) (μ := μ)) hs.compl
  rw [← heq] at ha
  filter_upwards [ha,hce,hco,hm.2] with omega ha hce hco hmgf
  rw [ha]
  simp only [Pi.add_apply,hce,hco,condExp_const (F.le i)]
  by_cases h : query i omega = x
  · simpa [s,e,queryWeight,h,NNReal.coe_pow,mul_comm] using hmgf
  · simp [s,queryWeight,h]

theorem actual_visit_process_has_initial_value_one_and_the_exact_multiplicative_step
    {Ω D : Type*} [DecidableEq D] (query : ℕ → Ω → D) (Y : ℕ → Ω → ℝ)
    (x : D) (R : ℝ≥0) (lambda : ℝ) :
    visitProcess query Y x R lambda 0 = 1 ∧ ∀ n omega,
      visitProcess query Y x R lambda (n + 1) omega =
        (visitProcess query Y x R lambda n omega *
          Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x n omega / 2)) *
            Real.exp (lambda * (queryWeight query x n * Y n) omega) := by
  constructor
  · ext omega
    simp [visitProcess,visitCount,partialSum]
  · intro n omega
    unfold visitProcess visitCount
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [(partialSum_initial_step (fun i => queryWeight query x i * Y i) n).2,
      (partialSum_initial_step (queryWeight query x) n).2, Pi.add_apply]
    ring

theorem actual_visit_process_is_adapted_and_integrable
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D) (lambda : ℝ) :
    StronglyAdapted F (visitProcess query Y x R lambda) ∧
      ∀ n, Integrable (visitProcess query Y x R lambda n) μ := by
  have hq := actual_adaptive_query_selection_weights_are_predictable F query hquery x
  have hw := actual_predictable_weighted_noise_has_the_derived_conditional_law
    μ F (queryWeight query x) Y hq.1 hY 1 R
    (fun i => Eventually.of_forall (hq.2 i)) hb hz
  have hqn : ∀ i, StronglyMeasurable[F (i + 1)] (queryWeight query x i) :=
    fun i => (hq.1 i).mono (F.mono (Nat.le_succ i))
  have hadp : StronglyAdapted F (visitProcess query Y x R lambda) := by
    intro n
    exact ((measurable_const.mul (partialSum_adapted F _ hw.1 n).measurable).sub
      (((measurable_const.mul (partialSum_adapted F _ hqn n).measurable)).div_const 2)).exp.stronglyMeasurable
  refine ⟨hadp,?_⟩
  intro n
  have hc : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i)
      (queryWeight query x i * Y i) (R ^ 2) := by simpa only [one_mul] using hw.2
  have hi := (actual_azuma_sum_subgaussian μ F _ hw.1 R hc n).integrable_exp_mul lambda
  apply hi.mono' ((hadp n).mono (F.le n)).aestronglyMeasurable
  filter_upwards [] with omega
  dsimp only [visitProcess]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hcount := (actual_visit_count_is_the_real_cardinality_of_the_selected_indices query x n omega).2
  have hcomp : 0 ≤ lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2 := by positivity
  linarith

/-- The real adaptive selection count gives a genuine nonnegative exponential supermartingale. -/
theorem actual_visit_count_compensated_noise_process_is_a_supermartingale
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D) (lambda : ℝ) :
    Supermartingale (visitProcess query Y x R lambda) F μ := by
  have hp := actual_visit_process_is_adapted_and_integrable μ F query hquery Y hY R hb hz x lambda
  refine supermartingale_nat hp.1 hp.2 ?_
  intro n
  let factor : Ω → ℝ := fun omega => visitProcess query Y x R lambda n omega *
    Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x n omega / 2)
  let noise : Ω → ℝ := fun omega => Real.exp (lambda * (queryWeight query x n * Y n) omega)
  have hq := actual_adaptive_query_selection_weights_are_predictable F query hquery x
  have hf : StronglyMeasurable[F n] factor :=
    (hp.1 n).mul (((measurable_const.mul (hq.1 n).measurable).div_const 2).exp.stronglyMeasurable)
  have heq : factor * noise = visitProcess query Y x R lambda (n + 1) := by
    ext omega
    exact (actual_visit_process_has_initial_value_one_and_the_exact_multiplicative_step
      query Y x R lambda).2 n omega |>.symm
  have hi : Integrable (factor * noise) μ := by rw [heq]; exact hp.2 (n + 1)
  have hm := actual_selected_noise_conditional_mgf_uses_its_actual_visit_indicator
    μ F query hquery Y hY R hb hz x lambda n
  have hce := condExp_mul_of_stronglyMeasurable_left hf hi hm.1
  rw [heq] at hce
  filter_upwards [hce,hm.2] with omega hce hmgf
  rw [hce]
  have hn : 0 ≤ factor omega := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    _ ≤ factor omega * Real.exp (lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x n omega / 2) :=
      mul_le_mul_of_nonneg_left hmgf hn
    _ = visitProcess query Y x R lambda n omega := by
      dsimp only [factor]
      rw [mul_assoc, ← Real.exp_add]
      have hzero : -lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x n omega / 2 +
          lambda ^ 2 * (R : ℝ) ^ 2 * queryWeight query x n omega / 2 = 0 := by ring
      rw [hzero,Real.exp_zero,mul_one]

/-- Ville's inequality yields a true all-time boundary with the actual visit count. -/
theorem actual_all_time_selected_noise_visit_count_boundary_probability
    {Ω D : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSingletonClass D] [DecidableEq D]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (query : ℕ → Ω → D) (hquery : ∀ i, @Measurable Ω D (F i) inferInstance (query i))
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i))
    (R : ℝ≥0) (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (x : D) (lambda delta : ℝ) (hd : 0 < delta) :
    μ.real {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum (fun i => queryWeight query x i * Y i) n omega -
        lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2} ≤ delta := by
  have heq : {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum (fun i => queryWeight query x i * Y i) n omega -
        lambda ^ 2 * (R : ℝ) ^ 2 * visitCount query x n omega / 2} =
      {omega | ∃ n, 1 / delta ≤ visitProcess query Y x R lambda n omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq,visitProcess]
    have hex : Real.exp (Real.log (1 / delta)) = 1 / delta := Real.exp_log (by positivity)
    constructor
    · rintro ⟨n,hn⟩
      refine ⟨n,?_⟩
      rw [← hex]
      exact Real.exp_le_exp.mpr hn
    · rintro ⟨n,hn⟩
      refine ⟨n,?_⟩
      apply Real.exp_le_exp.mp
      rwa [hex]
  rw [heq]
  have hv := ville μ F (visitProcess query Y x R lambda)
    (actual_visit_count_compensated_noise_process_is_a_supermartingale μ F query hquery Y hY R hb hz x lambda)
    (fun n => Eventually.of_forall fun omega => (Real.exp_pos _).le) (1 / delta) (by positivity)
  have hi : (∫ omega, visitProcess query Y x R lambda 0 omega ∂μ) = 1 := by
    rw [(actual_visit_process_has_initial_value_one_and_the_exact_multiplicative_step query Y x R lambda).1]
    simp
  rw [hi] at hv
  simpa using hv

end SafeLearning.CompleteModulesLandscapeVisitProcess
