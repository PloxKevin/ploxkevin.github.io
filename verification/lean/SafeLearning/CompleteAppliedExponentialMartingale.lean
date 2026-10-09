import SafeLearning.CompleteAppliedAzuma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedExponentialMartingale
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open SafeLearning.CompleteAppliedAzuma

theorem actual_conditional_mgf {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → ℝ) (hY : @Measurable Ω ℝ mΩ inferInstance Y) (c : ℝ≥0)
    (h : (@RealConditionalSubGaussian Ω mΩ μ inferInstance m hm Y) c) (lambda : ℝ) :
    Integrable (fun omega => Real.exp (lambda * Y omega)) μ ∧
      ∀ᵐ omega ∂μ, (μ[fun w => Real.exp (lambda * Y w) | m]) omega ≤
        Real.exp ((c : ℝ) * lambda ^ 2 / 2) := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Integrable (fun omega => Real.exp (lambda * Y omega)) μ := by
    have hip := h.integrable_exp_mul lambda
    rw [real_conditional_law_comp μ m hm Y hY] at hip
    exact (integrable_map_measure
      ((measurable_const.mul measurable_id).exp.aestronglyMeasurable) hY.aemeasurable).mp hip
  refine ⟨hi, ?_⟩
  have he : μ[fun w => Real.exp (lambda * Y w) | m] =ᵐ[μ]
      fun omega => ∫ y, Real.exp (lambda * y)
        ∂(@realConditionalLaw Ω mΩ μ inferInstance m Y) omega := by
    simpa only [MeasurableSpace.comap_id, id_eq, realConditionalLaw, Pi.mul_apply] using
      condExp_ae_eq_integral_condDistrib (mβ := m) (measurable_id'' hm) hY.aemeasurable
        ((measurable_const.mul measurable_id).exp.stronglyMeasurable) hi
  have hb := ae_of_ae_trim hm h.mgf_le
  filter_upwards [he, hb] with omega he hb
  rw [he]
  simpa [mgf] using hb lambda

def exponentialProcess {Ω : Type*} (Y : ℕ → Ω → ℝ) (R : ℝ≥0)
    (lambda : ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  Real.exp (lambda * partialSum Y n omega - lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2)

theorem exponential_initial_positive {Ω : Type*} (Y : ℕ → Ω → ℝ) (R : ℝ≥0)
    (lambda : ℝ) : exponentialProcess Y R lambda 0 = 1 ∧
      ∀ n omega, 0 < exponentialProcess Y R lambda n omega := by
  constructor
  · ext omega
    simp [exponentialProcess, partialSum]
  · intro n omega
    exact Real.exp_pos _

theorem exponential_step {Ω : Type*} (Y : ℕ → Ω → ℝ) (R : ℝ≥0)
    (lambda : ℝ) (n : ℕ) (omega : Ω) :
    exponentialProcess Y R lambda (n + 1) omega =
      (exponentialProcess Y R lambda n omega * Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 / 2)) *
        Real.exp (lambda * Y n omega) := by
  unfold exponentialProcess
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [(partialSum_initial_step Y n).2, Pi.add_apply, Nat.cast_add, Nat.cast_one]
  ring

theorem exponential_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0) (lambda : ℝ) :
    StronglyAdapted F (exponentialProcess Y R lambda) := by
  intro n
  exact ((measurable_const.mul (partialSum_adapted F Y hY n).measurable).sub
    measurable_const).exp.stronglyMeasurable

theorem exponential_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda : ℝ) (n : ℕ) : Integrable (exponentialProcess Y R lambda n) μ := by
  have hi := (actual_azuma_sum_subgaussian μ F Y hY R hcond n).integrable_exp_mul lambda
  convert hi.const_mul (Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 * (n : ℝ) / 2)) using 1
  ext omega
  unfold exponentialProcess
  rw [← Real.exp_add]
  congr 1
  ring

theorem exponential_conditional_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda : ℝ) (n : ℕ) :
    μ[exponentialProcess Y R lambda (n + 1) | F n] =ᵐ[μ]
      (fun omega => (exponentialProcess Y R lambda n omega *
        (μ[fun w => Real.exp (lambda * Y n w) | F n]) omega) *
          Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 / 2)) := by
  let factor : Ω → ℝ := fun omega => exponentialProcess Y R lambda n omega *
    Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 / 2)
  let noise : Ω → ℝ := fun omega => Real.exp (lambda * Y n omega)
  have hf : StronglyMeasurable[F n] factor :=
    (exponential_adapted F Y hY R lambda n).mul stronglyMeasurable_const
  have heq : factor * noise = exponentialProcess Y R lambda (n + 1) := by
    ext omega
    exact (exponential_step Y R lambda n omega).symm
  have hi : Integrable (factor * noise) μ := by
    rw [heq]
    exact exponential_integrable μ F Y hY R hcond lambda (n + 1)
  have hy := actual_conditional_mgf μ (F n) (F.le n) (Y n)
    ((hY n).mono (F.le (n + 1))).measurable (R ^ 2) (hcond n) lambda
  have hp := condExp_mul_of_stronglyMeasurable_left hf hi hy.1
  rw [heq] at hp
  filter_upwards [hp] with omega hp
  rw [hp]
  simp only [Pi.mul_apply, factor]
  ring

theorem actual_exponential_supermartingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0)
    (hcond : ∀ i, RealConditionalSubGaussian μ (F i) (F.le i) (Y i) (R ^ 2))
    (lambda : ℝ) : Supermartingale (exponentialProcess Y R lambda) F μ := by
  refine supermartingale_nat (exponential_adapted F Y hY R lambda)
    (exponential_integrable μ F Y hY R hcond lambda) ?_
  intro n
  have he := exponential_conditional_step μ F Y hY R hcond lambda n
  have hb := (actual_conditional_mgf μ (F n) (F.le n) (Y n)
    ((hY n).mono (F.le (n + 1))).measurable (R ^ 2) (hcond n) lambda).2
  filter_upwards [he, hb] with omega he hb
  rw [he]
  have hn : 0 ≤ exponentialProcess Y R lambda n omega := (Real.exp_pos _).le
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hn)
    (Real.exp_pos (-lambda ^ 2 * (R : ℝ) ^ 2 / 2)).le
  calc
    _ ≤ (exponentialProcess Y R lambda n omega * Real.exp ((R ^ 2 : ℝ≥0) * lambda ^ 2 / 2)) *
        Real.exp (-lambda ^ 2 * (R : ℝ) ^ 2 / 2) := hprod
    _ = exponentialProcess Y R lambda n omega := by
      rw [mul_assoc, ← Real.exp_add]
      simp only [NNReal.coe_pow]
      have hz : (R : ℝ) ^ 2 * lambda ^ 2 / 2 + -lambda ^ 2 * (R : ℝ) ^ 2 / 2 = 0 := by ring
      rw [hz, Real.exp_zero, mul_one]

theorem bounded_difference_exponential_supermartingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, StronglyMeasurable[F (i + 1)] (Y i)) (R : ℝ≥0)
    (hb : ∀ i, ∀ᵐ omega ∂μ, Y i omega ∈ Set.Icc (-(R : ℝ)) R)
    (hz : ∀ i, μ[Y i | F i] =ᵐ[μ] 0) (lambda : ℝ) :
    Supermartingale (exponentialProcess Y R lambda) F μ := by
  apply actual_exponential_supermartingale μ F Y hY R _ lambda
  intro i
  exact bounded_centered_is_real_conditional_subgaussian μ (F i) (F.le i) (Y i)
    ((hY i).mono (F.le (i + 1))).measurable R (hb i) (hz i)

end SafeLearning.CompleteAppliedExponentialMartingale
