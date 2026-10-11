import Mathlib
set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteAppliedCountableMixtureMaterial24
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

def countableMixture (w : ι → ℝ≥0) (μ : ι → Measure Ω) : Measure Ω :=
  Measure.sum (fun i => (w i : ℝ≥0∞) • μ i)

theorem actual_countable_mixture_is_a_probability_law
    (w : ι → ℝ≥0) (hw : ∑' i, (w i : ℝ≥0∞) = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (countableMixture w μ) := by
  constructor
  simp only [countableMixture, Measure.sum_apply_of_countable, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact hw

theorem actual_countable_mixture_integral_hasSum
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) (X : Ω → ℝ)
    (hX : Integrable X (countableMixture w μ)) :
    HasSum (fun i => (w i : ℝ) * ∫ ω, X ω ∂μ i)
      (∫ ω, X ω ∂countableMixture w μ) := by
  simpa only [countableMixture, integral_smul_measure, ENNReal.coe_toReal,
    smul_eq_mul] using hasSum_integral_measure hX

theorem actual_countable_mixture_mean
    (w : ι → ℝ≥0) (hw : ∑' i, (w i : ℝ≥0∞) = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Ω → ℝ) (hX : MemLp X 2 (countableMixture w μ)) :
    (∫ ω, X ω ∂countableMixture w μ) =
      ∑' i, (w i : ℝ) * ∫ ω, X ω ∂μ i := by
  haveI := actual_countable_mixture_is_a_probability_law w hw μ
  exact (actual_countable_mixture_integral_hasSum w μ X
    (hX.integrable one_le_two)).tsum_eq.symm

private theorem component_centered_second_moment
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (M : ℝ) :
    (∫ ω, (X ω - M)^2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ) - M)^2 := by
  have hx := hX.integrable one_le_two
  have hp : (fun ω => (X ω - M)^2) =
      (fun ω => (X ω)^2 - (2*M)*X ω + M^2) := by ext ω; ring
  rw [hp]
  change (∫ ω, ((fun ω => (X ω)^2) - (fun ω => (2*M)*X ω)) ω + M^2 ∂μ) = _
  rw [integral_add (hX.integrable_sq.sub (hx.const_mul (2*M)))
    (integrable_const _), integral_sub hX.integrable_sq (hx.const_mul (2*M)),
    integral_const_mul, integral_const, variance_eq_sub hX]
  simp only [measureReal_univ_eq_one, one_smul]
  ring

theorem actual_countable_mixture_variance_and_series_summability
    (w : ι → ℝ≥0) (hw : ∑' i, (w i : ℝ≥0∞) = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Ω → ℝ) (hX : MemLp X 2 (countableMixture w μ))
    (hXi : ∀ i, MemLp X 2 (μ i)) :
    Summable (fun i => (w i : ℝ) * variance X (μ i)) ∧
    Summable (fun i => (w i : ℝ) *
      ((∫ ω, X ω ∂μ i) - ∑' j, (w j : ℝ) * ∫ ω, X ω ∂μ j)^2) ∧
    variance X (countableMixture w μ) =
      (∑' i, (w i : ℝ) * variance X (μ i)) +
      ∑' i, (w i : ℝ) *
        ((∫ ω, X ω ∂μ i) - ∑' j, (w j : ℝ) * ∫ ω, X ω ∂μ j)^2 := by
  haveI := actual_countable_mixture_is_a_probability_law w hw μ
  let M : ℝ := ∫ ω, X ω ∂countableMixture w μ
  let a : ι → ℝ := fun i => (w i : ℝ) * variance X (μ i)
  let b : ι → ℝ := fun i => (w i : ℝ) * ((∫ ω, X ω ∂μ i) - M)^2
  have hs := actual_countable_mixture_integral_hasSum w μ (fun ω => (X ω - M)^2)
    (hX.sub (memLp_const M)).integrable_sq
  have he (i : ι) : (w i : ℝ) * (∫ ω, (X ω - M)^2 ∂μ i) = a i + b i := by
    rw [component_centered_second_moment (μ i) X (hXi i) M]
    simp only [a, b, mul_add]
  simp_rw [he] at hs
  have ha0 (i : ι) : 0 ≤ a i := mul_nonneg (NNReal.coe_nonneg _) (variance_nonneg _ _)
  have hb0 (i : ι) : 0 ≤ b i := mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)
  have has : Summable a := Summable.of_nonneg_of_le ha0
    (fun i => le_add_of_nonneg_right (hb0 i)) hs.summable
  have hbs : Summable b := Summable.of_nonneg_of_le hb0
    (fun i => le_add_of_nonneg_left (ha0 i)) hs.summable
  have hm := actual_countable_mixture_mean w hw μ X hX
  have hvar : variance X (countableMixture w μ) = (∑' i, a i) + ∑' i, b i := by
    rw [variance_eq_integral hX.aemeasurable, ← hs.tsum_eq]
    exact has.tsum_add hbs
  simpa only [a, b, M, hm] using And.intro has (And.intro hbs hvar)

theorem actual_countable_mixture_of_densities_has_the_printed_density
    (w : ι → ℝ≥0) (base : Measure Ω) (p : ι → Ω → ℝ≥0∞)
    (hp : ∀ i, Measurable (p i)) :
    countableMixture w (fun i => base.withDensity (p i)) =
      base.withDensity (fun ω => ∑' i, (w i : ℝ≥0∞) * p i ω) := by
  have he (i : ι) : (w i : ℝ≥0∞) • base.withDensity (p i) =
      base.withDensity ((w i : ℝ≥0∞) • p i) :=
    (withDensity_smul (w i : ℝ≥0∞) (hp i)).symm
  simp_rw [countableMixture, he]
  change (Measure.sum (fun i => base.withDensity (fun ω => (w i : ℝ≥0∞) * p i ω))) = _
  rw [← withDensity_tsum (μ := base)
    (f := fun i ω => (w i : ℝ≥0∞) * p i ω)
    (fun i => measurable_const.mul (hp i))]
  congr 1
  ext ω
  simp only [tsum_apply]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

def twoStageLaw (w : ι → ℝ≥0) (μ : ι → Measure Ω) : Measure (ι × Ω) :=
  countableMixture w (fun i => (Measure.dirac i).prod (μ i))

theorem actual_two_stage_joint_is_a_probability_law
    (w : ι → ℝ≥0) (hw : ∑' i, (w i : ℝ≥0∞) = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (twoStageLaw w μ) :=
  actual_countable_mixture_is_a_probability_law w hw _

theorem actual_two_stage_label_and_component_rectangle
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (s : Set Ω) :
    twoStageLaw w μ ({j} ×ˢ s) = (w j : ℝ≥0∞) * μ j s := by
  classical
  simp only [twoStageLaw, countableMixture, Measure.sum_apply_of_countable,
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Measure.dirac_apply,
    Set.indicator_singleton, Pi.one_apply]
  rw [tsum_eq_single j]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb, Ne.symm hb]

theorem actual_two_stage_label_probability
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) : (twoStageLaw w μ).fst {j} = (w j : ℝ≥0∞) := by
  rw [Measure.fst_apply (measurableSet_singleton j)]
  have hpre : Prod.fst ⁻¹' ({j} : Set ι) = {j} ×ˢ (Set.univ : Set Ω) := by
    ext p; simp
  rw [hpre, actual_two_stage_label_and_component_rectangle]
  simp

theorem actual_two_stage_second_marginal_is_the_countable_mixture
    (w : ι → ℝ≥0) (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    (twoStageLaw w μ).snd = countableMixture w μ := by
  ext s hs
  rw [Measure.snd_apply hs]
  have hpre : Prod.snd ⁻¹' s = (Set.univ : Set ι) ×ˢ s := by ext p; simp
  rw [hpre]
  simp [twoStageLaw, countableMixture, Measure.sum_apply_of_countable,
    Measure.smul_apply, Measure.prod_prod]

end SafeLearning.CompleteAppliedCountableMixtureMaterial24
