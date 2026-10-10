import SafeLearning.CompleteModulesLandscapePredictableNoise

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeQuadraticWeights
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open CompleteAppliedAzuma CompleteAppliedExponentialMartingale CompleteAppliedStopping
open CompleteModulesLandscapePredictableNoise

/-- Conditioning uses every fixed tilt on the actual conditional law, so a
past-measurable weight is genuinely squared inside the random compensator. -/
theorem actual_predictable_weighted_noise_conditional_mgf_uses_the_actual_squared_weight
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (q Y : Ω → ℝ) (hq : StronglyMeasurable[m] q)
    (hY : @Measurable Ω ℝ mΩ inferInstance Y) (K R : ℝ≥0)
    (hqbound : ∀ᵐ omega ∂μ, |q omega| ≤ K)
    (hYbound : ∀ᵐ omega ∂μ, Y omega ∈ Icc (-(R : ℝ)) R)
    (hzero : μ[Y | m] =ᵐ[μ] 0) (lambda : ℝ) :
    Integrable (fun omega => Real.exp (lambda * (q * Y) omega)) μ ∧
      ∀ᵐ omega ∂μ,
        (μ[fun w => Real.exp (lambda * (q * Y) w) | m]) omega ≤
          Real.exp (lambda ^ 2 * (R : ℝ) ^ 2 * q omega ^ 2 / 2) := by
  letI : MeasurableSpace Ω := mΩ
  have hp := actual_bounded_predictable_weight_preserves_conditional_zero_and_support
    μ m hm q Y hq hY K R hqbound hYbound hzero
  have hprod : Measurable (q * Y) := (hq.measurable.mono hm le_rfl).mul hY
  have hi : Integrable (fun omega => Real.exp (lambda * (q * Y) omega)) μ :=
    integrable_exp_mul_of_mem_Icc hprod.aemeasurable hp.2
  have hkernel := bounded_centered_is_real_conditional_subgaussian μ m hm Y hY R hYbound hzero
  have he : μ[fun omega => Real.exp (lambda * (q * Y) omega) | m] =ᵐ[μ]
      fun omega => ∫ y, Real.exp (lambda * q omega * y)
        ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega := by
    have hf : StronglyMeasurable[m.prod inferInstance]
        (fun p : Ω × ℝ => Real.exp (lambda * q p.1 * p.2)) :=
      ((measurable_const.mul (hq.measurable.comp measurable_fst)).mul measurable_snd).exp.stronglyMeasurable
    have hi' : Integrable (fun omega => Real.exp (lambda * q omega * Y omega)) μ := by
      simpa only [Pi.mul_apply,mul_assoc] using hi
    simpa only [MeasurableSpace.comap_id,id_eq,realConditionalLaw,Pi.mul_apply,mul_assoc] using
      condExp_prod_ae_eq_integral_condDistrib (mβ := m) (measurable_id'' hm)
        hY.aemeasurable hf hi'
  have hb := ae_of_ae_trim hm hkernel.mgf_le
  refine ⟨hi,?_⟩
  filter_upwards [he,hb] with omega he hb
  rw [he]
  have h := hb (lambda * q omega)
  have halgebra : ((R ^ 2 : ℝ≥0) : ℝ) * (lambda * q omega) ^ 2 / 2 =
      lambda ^ 2 * (R : ℝ) ^ 2 * q omega ^ 2 / 2 := by simp only [NNReal.coe_pow]; ring
  simpa only [mgf,id_eq,halgebra] using h

def quadraticProcess {Ω : Type*} (q Y : ℕ → Ω → ℝ) (R : ℝ≥0)
    (lambda : ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  Real.exp (lambda * partialSum (fun i => q i * Y i) n omega -
    lambda ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega / 2)

/-- This is the actual weighted sum and quadratic sum at each step. -/
theorem actual_quadratic_weight_process_has_initial_one_and_the_exact_step
    {Ω : Type*} (q Y : ℕ → Ω → ℝ) (R : ℝ≥0) (lambda : ℝ) :
    quadraticProcess q Y R lambda 0 = 1 ∧ ∀ n omega,
      quadraticProcess q Y R lambda (n + 1) omega =
        (quadraticProcess q Y R lambda n omega *
          Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 * q n omega ^ 2 / 2)) *
            Real.exp (lambda * (q n * Y n) omega) := by
  constructor
  · ext omega
    simp [quadraticProcess,partialSum]
  · intro n omega
    unfold quadraticProcess
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    simp only [(partialSum_initial_step (fun i => q i * Y i) n).2,
      (partialSum_initial_step (fun i omega => q i omega ^ 2) n).2,Pi.add_apply]
    ring

/-- Uniform boundedness supplies integrability; the random quadratic sum,
not the uniform bound times elapsed time, stays in the actual process. -/
theorem actual_quadratic_weight_process_is_adapted_and_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (lambda : ℝ) :
    StronglyAdapted F (quadraticProcess q Y R lambda) ∧
      ∀ n, Integrable (quadraticProcess q Y R lambda n) μ := by
  have hw := actual_predictable_weighted_noise_has_the_derived_conditional_law
    μ F q Y hq hY K R hqbound hYbound hzero
  have hqnext : ∀ i, StronglyMeasurable[F (i + 1)] (fun omega => q i omega ^ 2) :=
    fun i => ((hq i).mono (F.mono (Nat.le_succ i))).pow 2
  have hadp : StronglyAdapted F (quadraticProcess q Y R lambda) := by
    intro n
    exact ((measurable_const.mul (partialSum_adapted F _ hw.1 n).measurable).sub
      ((measurable_const.mul (partialSum_adapted F _ hqnext n).measurable).div_const 2)).exp.stronglyMeasurable
  refine ⟨hadp,?_⟩
  intro n
  have hi := (actual_azuma_sum_subgaussian μ F _ hw.1 (K * R) hw.2 n).integrable_exp_mul lambda
  apply hi.mono' ((hadp n).mono (F.le n)).aestronglyMeasurable
  filter_upwards [] with omega
  dsimp only [quadraticProcess]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hquad : 0 ≤ partialSum (fun i omega => q i omega ^ 2) n omega := by
    unfold partialSum
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomp : 0 ≤ lambda ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega / 2 := by positivity
  linarith

/-- A true exponential supermartingale uses actual predictable quadratic
weights for arbitrary bounded past-dependent real weights, including features. -/
theorem actual_predictable_quadratic_weight_process_is_a_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (lambda : ℝ) :
    Supermartingale (quadraticProcess q Y R lambda) F μ := by
  have hp := actual_quadratic_weight_process_is_adapted_and_integrable
    μ F q Y hq hY K R hqbound hYbound hzero lambda
  refine supermartingale_nat hp.1 hp.2 ?_
  intro n
  let factor : Ω → ℝ := fun omega => quadraticProcess q Y R lambda n omega *
    Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 * q n omega ^ 2 / 2)
  let noise : Ω → ℝ := fun omega => Real.exp (lambda * (q n * Y n) omega)
  have hf : StronglyMeasurable[F n] factor :=
    (hp.1 n).mul ((measurable_const.mul ((hq n).pow 2).measurable).div_const 2).exp.stronglyMeasurable
  have heq : factor * noise = quadraticProcess q Y R lambda (n + 1) := by
    ext omega
    exact (actual_quadratic_weight_process_has_initial_one_and_the_exact_step q Y R lambda).2 n omega |>.symm
  have hi : Integrable (factor * noise) μ := by rw [heq]; exact hp.2 (n + 1)
  have hm := actual_predictable_weighted_noise_conditional_mgf_uses_the_actual_squared_weight
    μ (F n) (F.le n) (q n) (Y n) (hq n) ((hY n).mono (F.le (n + 1))).measurable
    K R (hqbound n) (hYbound n) (hzero n) lambda
  have hce := condExp_mul_of_stronglyMeasurable_left hf hi hm.1
  rw [heq] at hce
  filter_upwards [hce,hm.2] with omega hce hmgf
  rw [hce]
  have hn : 0 ≤ factor omega := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    _ ≤ factor omega * Real.exp (lambda ^ 2 * (R : ℝ) ^ 2 * q n omega ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hmgf hn
    _ = quadraticProcess q Y R lambda n omega := by
      dsimp only [factor]
      rw [mul_assoc,← Real.exp_add]
      have hzero : -lambda ^ 2 * (R : ℝ) ^ 2 * q n omega ^ 2 / 2 +
          lambda ^ 2 * (R : ℝ) ^ 2 * q n omega ^ 2 / 2 = 0 := by ring
      rw [hzero,Real.exp_zero,mul_one]

/-- Genuine all-time Ville confidence for the actual weighted sum and its
actual quadratic compensator. This does not assert matrix self-normalization. -/
theorem actual_all_time_predictable_weighted_noise_quadratic_boundary_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (q Y : ℕ → Ω → ℝ) (hq : ∀ i, StronglyMeasurable[F i] (q i))
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (K R : ℝ≥0)
    (hqbound : ∀ i, ∀ᵐ omega ∂μ, |q i omega| ≤ K)
    (hYbound : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Icc (-(R : ℝ)) R)
    (hzero : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (lambda delta : ℝ) (hd : 0 < delta) :
    μ.real {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum (fun i => q i * Y i) n omega -
        lambda ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega / 2} ≤ delta := by
  have heq : {omega | ∃ n, Real.log (1 / delta) ≤
      lambda * partialSum (fun i => q i * Y i) n omega -
        lambda ^ 2 * (R : ℝ) ^ 2 * partialSum (fun i omega => q i omega ^ 2) n omega / 2} =
      {omega | ∃ n, 1 / delta ≤ quadraticProcess q Y R lambda n omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq,quadraticProcess]
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
  have hv := ville μ F (quadraticProcess q Y R lambda)
    (actual_predictable_quadratic_weight_process_is_a_supermartingale μ F q Y hq hY K R hqbound hYbound hzero lambda)
    (fun n => Eventually.of_forall fun omega => (Real.exp_pos _).le) (1 / delta) (by positivity)
  have hi : (∫ omega, quadraticProcess q Y R lambda 0 omega ∂μ) = 1 := by
    rw [(actual_quadratic_weight_process_has_initial_one_and_the_exact_step q Y R lambda).1]
    simp
  rw [hi] at hv
  simpa using hv

end SafeLearning.CompleteModulesLandscapeQuadraticWeights
