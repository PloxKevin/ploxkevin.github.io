import Mathlib
set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteAppliedFiniteMixtureMaterial24
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

def finiteMixture (w : ι → ℝ≥0) (μ : ι → Measure Ω) : Measure Ω :=
  ∑ i, (w i : ℝ≥0∞) • μ i

theorem actual_finite_mixture_is_a_probability_law
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (finiteMixture w μ) := by
  constructor
  simp only [finiteMixture, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast hw

theorem actual_finite_mixture_integral
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) (X : Ω → ℝ)
    (hX : ∀ i, Integrable X (μ i)) :
    (∫ ω, X ω ∂finiteMixture w μ) =
      ∑ i, (w i : ℝ) * ∫ ω, X ω ∂μ i := by
  rw [finiteMixture, integral_finsetSum_measure
    (fun i _ => (hX i).smul_measure ENNReal.coe_ne_top)]
  simp [NNReal.smul_def, smul_eq_mul]

theorem actual_finite_mixture_has_finite_second_moment
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) (X : Ω → ℝ)
    (hX : ∀ i, MemLp X 2 (μ i)) : MemLp X 2 (finiteMixture w μ) := by
  have hs : AEStronglyMeasurable X (finiteMixture w μ) := by
    rw [finiteMixture, ← Measure.sum_fintype]
    exact AEStronglyMeasurable.sum_measure
      (fun i => ((hX i).smul_measure ENNReal.coe_ne_top).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hs).mpr
  rw [finiteMixture, integrable_finsetSum_measure]
  intro i _
  exact ((hX i).smul_measure ENNReal.coe_ne_top).integrable_sq

theorem actual_finite_mixture_mean
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Ω → ℝ) (hX : ∀ i, MemLp X 2 (μ i)) :
    (∫ ω, X ω ∂finiteMixture w μ) =
      ∑ i, (w i : ℝ) * ∫ ω, X ω ∂μ i :=
  actual_finite_mixture_integral w μ X (fun i => (hX i).integrable one_le_two)

theorem actual_finite_mixture_variance
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Ω → ℝ) (hX : ∀ i, MemLp X 2 (μ i)) :
    variance X (finiteMixture w μ) =
      (∑ i, (w i : ℝ) * variance X (μ i)) +
      ∑ i, (w i : ℝ) *
        ((∫ ω, X ω ∂μ i) - ∑ j, (w j : ℝ) * ∫ ω, X ω ∂μ j)^2 := by
  haveI := actual_finite_mixture_is_a_probability_law w hw μ
  have hr : ∑ i, (w i : ℝ) = 1 := by exact_mod_cast hw
  let m : ι → ℝ := fun i => ∫ ω, X ω ∂μ i
  let M : ℝ := ∑ i, (w i : ℝ) * m i
  have he : (∑ i, (w i : ℝ) * (m i - M)^2) =
      (∑ i, (w i : ℝ) * (m i)^2) - M^2 := by
    have hexp (i : ι) : (w i : ℝ) * (m i - M)^2 =
        (w i : ℝ) * (m i)^2 - (2*M)*((w i : ℝ)*m i) +
          M^2 * (w i : ℝ) := by ring
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hr]
    change (∑ i, (w i : ℝ) * (m i)^2) - (2*M)*M + M^2*1 = _
    ring
  rw [variance_eq_sub (actual_finite_mixture_has_finite_second_moment w μ X hX),
    actual_finite_mixture_mean w μ X hX]
  have hsq := actual_finite_mixture_integral w μ (fun ω => (X ω)^2)
    (fun i => (hX i).integrable_sq)
  simp only [Pi.pow_apply] at hsq ⊢
  rw [hsq]
  have hv (i : ι) : variance X (μ i) = (∫ ω, (X ω)^2 ∂μ i) - (m i)^2 :=
    variance_eq_sub (hX i)
  simp_rw [hv, mul_sub]
  rw [Finset.sum_sub_distrib]
  change (∑ i, (w i : ℝ) * ∫ ω, (X ω)^2 ∂μ i) - M^2 =
      ((∑ i, (w i : ℝ) * ∫ ω, (X ω)^2 ∂μ i) -
        ∑ i, (w i : ℝ) * (m i)^2) + ∑ i, (w i : ℝ) * (m i - M)^2
  rw [he]
  ring

theorem actual_finite_mixture_of_densities_has_the_printed_density
    (w : ι → ℝ≥0) (base : Measure Ω) (p : ι → Ω → ℝ≥0∞)
    (hp : ∀ i, Measurable (p i)) :
    finiteMixture w (fun i => base.withDensity (p i)) =
      base.withDensity (fun ω => ∑ i, (w i : ℝ≥0∞) * p i ω) := by
  rw [finiteMixture, ← Measure.sum_fintype]
  have he (i : ι) : (w i : ℝ≥0∞) • base.withDensity (p i) =
      base.withDensity ((w i : ℝ≥0∞) • p i) :=
    (withDensity_smul (w i : ℝ≥0∞) (hp i)).symm
  simp_rw [he]
  change (Measure.sum (fun i => base.withDensity (fun ω => (w i : ℝ≥0∞) * p i ω))) = _
  rw [← withDensity_tsum (μ := base)
    (f := fun i ω => (w i : ℝ≥0∞) * p i ω)
    (fun i => measurable_const.mul (hp i))]
  congr 1
  ext ω
  simp [tsum_fintype, smul_eq_mul]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

def twoStageLaw (w : ι → ℝ≥0) (μ : ι → Measure Ω) : Measure (ι × Ω) :=
  finiteMixture w (fun i => (Measure.dirac i).prod (μ i))

omit [MeasurableSingletonClass ι] in
theorem actual_two_stage_joint_is_a_probability_law
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (twoStageLaw w μ) :=
  actual_finite_mixture_is_a_probability_law w hw _

theorem actual_two_stage_label_and_component_rectangle
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (s : Set Ω) (hs : MeasurableSet s) :
    twoStageLaw w μ ({j} ×ˢ s) = (w j : ℝ≥0∞) * μ j s := by
  classical
  simp only [twoStageLaw, finiteMixture, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.prod_prod, Measure.dirac_apply, Set.indicator_singleton, Pi.one_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · simp

omit [MeasurableSingletonClass ι] in
theorem actual_two_stage_second_marginal_is_the_finite_mixture
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    (twoStageLaw w μ).snd = finiteMixture w μ := by
  ext s hs
  rw [Measure.snd_apply hs]
  have hpre : Prod.snd ⁻¹' s = (Set.univ : Set ι) ×ˢ s := by
    ext p
    simp
  rw [hpre]
  simp [twoStageLaw, finiteMixture, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.prod_prod]

end SafeLearning.CompleteAppliedFiniteMixtureMaterial24
