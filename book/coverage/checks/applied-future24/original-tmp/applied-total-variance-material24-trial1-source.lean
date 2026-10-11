import Mathlib
set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteAppliedTotalVarianceMaterial24

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω)

/-- The actual conditional expectation of the centered product, rather than an
assumed covariance decomposition. -/
def conditionalCovariance (X Y : Ω → ℝ) : Ω → ℝ :=
  μ[(X - μ[X | m]) * (Y - μ[Y | m]) | m]

theorem actual_conditional_mean_and_second_moment_tower
    (hm : m ≤ ‹MeasurableSpace Ω›) (X : Ω → ℝ) :
    (∫ ω, (μ[X | m]) ω ∂μ) = ∫ ω, X ω ∂μ ∧
    (∫ ω, (μ[X ^ 2 | m]) ω ∂μ) = ∫ ω, (X ω) ^ 2 ∂μ := by
  exact ⟨integral_condExp hm, integral_condExp hm⟩

theorem actual_conditional_second_moment_is_variance_plus_squared_mean
    (hm : m ≤ ‹MeasurableSpace Ω›) (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    μ[X ^ 2 | m] =ᵐ[μ] fun ω =>
      (condVar m X μ) ω + ((μ[X | m]) ω) ^ 2 := by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX] with ω h
  dsimp at h ⊢
  linarith

theorem actual_scalar_law_of_total_variance
    (hm : m ≤ ‹MeasurableSpace Ω›) (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    variance X μ = (∫ ω, (condVar m X μ) ω ∂μ) +
      variance (μ[X | m]) μ := by
  exact (integral_condVar_add_variance_condExp hm hX).symm

theorem actual_conditional_covariance_is_conditional_product_minus_mean_product
    (hm : m ≤ ‹MeasurableSpace Ω›) (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    conditionalCovariance μ m X Y =ᵐ[μ]
      μ[X * Y | m] - μ[X | m] * μ[Y | m] := by
  have hxm := hX.condExp one_le_two
  have hym := hY.condExp one_le_two
  have hiXY : Integrable (X * Y) μ := memLp_one_iff_integrable.mp (hX.mul hY)
  have hiXym : Integrable (X * μ[Y | m]) μ := memLp_one_iff_integrable.mp (hX.mul hym)
  have hiXmY : Integrable (μ[X | m] * Y) μ := memLp_one_iff_integrable.mp (hxm.mul hY)
  have hiXmYm : Integrable (μ[X | m] * μ[Y | m]) μ :=
    memLp_one_iff_integrable.mp (hxm.mul hym)
  have hexpand :
      (X - μ[X | m]) * (Y - μ[Y | m]) =
        X * Y - X * μ[Y | m] - μ[X | m] * Y + μ[X | m] * μ[Y | m] := by
    ext ω
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    ring
  rw [conditionalCovariance, hexpand]
  filter_upwards [condExp_add (m := m) ((hiXY.sub hiXym).sub hiXmY) hiXmYm,
    condExp_sub (m := m) (hiXY.sub hiXym) hiXmY,
    condExp_sub (m := m) hiXY hiXym,
    condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_condExp (m := m) (f := Y)) hiXym (hX.integrable one_le_two),
    condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_condExp (m := m) (f := X)) hiXmY (hY.integrable one_le_two)]
    with ω hadd hsub hsub' hright hleft
  rw [condExp_of_stronglyMeasurable hm
    ((stronglyMeasurable_condExp (m := m) (f := X)).mul
      (stronglyMeasurable_condExp (m := m) (f := Y))) hiXmYm] at hadd
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hadd hsub hsub' hright hleft ⊢
  rw [hadd, hsub, hsub', hright, hleft]
  ring

theorem actual_scalar_law_of_total_covariance
    (hm : m ≤ ‹MeasurableSpace Ω›) (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ =
      (∫ ω, conditionalCovariance μ m X Y ω ∂μ) +
      covariance (μ[X | m]) (μ[Y | m]) μ := by
  have hprod : Integrable (μ[X | m] * μ[Y | m]) μ :=
    memLp_one_iff_integrable.mp ((hX.condExp one_le_two).mul (hY.condExp one_le_two))
  have hce := actual_conditional_covariance_is_conditional_product_minus_mean_product
    μ m hm X Y hX hY
  rw [integral_congr_ae hce, integral_sub integrable_condExp hprod,
    integral_condExp hm, covariance_eq_sub hX hY,
    covariance_eq_sub (hX.condExp one_le_two) (hY.condExp one_le_two),
    integral_condExp hm, integral_condExp hm]
  ring

def covarianceMatrix {ι : Type*} (X : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  fun i j => covariance (X i) (X j) μ

def conditionalCovarianceMatrix {ι : Type*} (X : ι → Ω → ℝ) : Ω → Matrix ι ι ℝ :=
  fun ω i j => conditionalCovariance μ m (X i) (X j) ω

/-- The expectation here is a genuine matrix-valued Bochner integral. -/
theorem actual_finite_vector_law_of_total_covariance
    {ι : Type*} [Fintype ι] (hm : m ≤ ‹MeasurableSpace Ω›)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    covarianceMatrix μ X =
      (∫ ω, conditionalCovarianceMatrix μ m X ω ∂μ) +
      covarianceMatrix μ (fun i => μ[X i | m]) := by
  have hi (i j : ι) : Integrable (fun ω => conditionalCovariance μ m (X i) (X j) ω) μ :=
    integrable_condExp
  have hir (i : ι) : Integrable (fun ω j => conditionalCovariance μ m (X i) (X j) ω) μ :=
    Integrable.of_eval (hi i)
  ext i j
  change covariance (X i) (X j) μ =
    (∫ ω, conditionalCovarianceMatrix μ m X ω ∂μ) i j +
      covariance (μ[X i | m]) (μ[X j | m]) μ
  have heval : (∫ ω, conditionalCovarianceMatrix μ m X ω ∂μ) i j =
      ∫ ω, conditionalCovariance μ m (X i) (X j) ω ∂μ := by
    change (∫ ω, fun i j => conditionalCovariance μ m (X i) (X j) ω ∂μ) i j = _
    rw [eval_integral hir i, eval_integral (hi i) j]
  rw [heval]
  exact actual_scalar_law_of_total_covariance μ m hm (X i) (X j) (hX i) (hX j)

theorem actual_scalar_law_conditioning_on_a_measurable_random_variable
    {Υ : Type*} [MeasurableSpace Υ] (Y : Ω → Υ) (hY : Measurable Y)
    (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    variance X μ =
      (∫ ω, condVar (MeasurableSpace.comap Y ‹MeasurableSpace Υ›) X μ ω ∂μ) +
      variance (μ[X | MeasurableSpace.comap Y ‹MeasurableSpace Υ›]) μ := by
  exact actual_scalar_law_of_total_variance μ _ hY X hX

end SafeLearning.CompleteAppliedTotalVarianceMaterial24
