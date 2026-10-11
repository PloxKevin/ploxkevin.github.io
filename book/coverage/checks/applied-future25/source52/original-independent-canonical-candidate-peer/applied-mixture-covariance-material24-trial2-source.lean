import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedMixtureCovarianceMaterial24
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix.Norms.Elementwise
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
def finiteMixture (w : ι → ℝ≥0) (μ : ι → Measure Ω) : Measure Ω :=
  ∑ i, (w i : ℝ≥0∞) • μ i
private theorem probability_law (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (finiteMixture w μ) := by
  constructor
  simp only [finiteMixture, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast hw
private theorem weighted_integral (w : ι → ℝ≥0) (μ : ι → Measure Ω)
    (X : Ω → ℝ) (hX : ∀ i, Integrable X (μ i)) :
    (∫ ω, X ω ∂finiteMixture w μ) = ∑ i, (w i : ℝ) * ∫ ω, X ω ∂μ i := by
  rw [finiteMixture, integral_finsetSum_measure
    (fun i _ => (hX i).smul_measure ENNReal.coe_ne_top)]
  simp [NNReal.smul_def, smul_eq_mul]
private theorem mixture_memLp (w : ι → ℝ≥0) (μ : ι → Measure Ω)
    (X : Ω → ℝ) (hX : ∀ i, MemLp X 2 (μ i)) : MemLp X 2 (finiteMixture w μ) := by
  have hs : AEStronglyMeasurable X (finiteMixture w μ) := by
    rw [finiteMixture, ← Measure.sum_fintype]
    exact AEStronglyMeasurable.sum_measure
      (fun i => ((hX i).smul_measure ENNReal.coe_ne_top).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hs).mpr
  rw [finiteMixture, integrable_finsetSum_measure]
  intro i _
  exact ((hX i).smul_measure ENNReal.coe_ne_top).integrable_sq
private theorem component_centered_product (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (M N : ℝ) :
    (∫ ω, (X ω - M)*(Y ω - N) ∂μ) =
      covariance X Y μ + ((∫ ω, X ω ∂μ)-M)*((∫ ω, Y ω ∂μ)-N) := by
  have hx := hX.integrable one_le_two
  have hy := hY.integrable one_le_two
  have hxy := hX.integrable_mul hY
  have he : (fun ω => (X ω-M)*(Y ω-N)) =
      (fun ω => X ω*Y ω-N*X ω-M*Y ω+M*N) := by ext ω; ring
  rw [he]
  change (∫ ω, (((X*Y)-(fun ω=>N*X ω))-(fun ω=>M*Y ω)) ω + M*N ∂μ) = _
  rw [integral_add ((hxy.sub (hx.const_mul N)).sub (hy.const_mul M))
    (integrable_const _)]
  rw [integral_sub (hxy.sub (hx.const_mul N)) (hy.const_mul M),
    integral_sub hxy (hx.const_mul N)]
  simp only [Pi.mul_apply]
  rw [integral_const_mul, integral_const_mul,
    integral_const, covariance_eq_sub hX hY]
  simp only [probReal_univ, one_smul, Pi.mul_apply]
  ring

theorem actual_finite_mixture_covariance_within_and_between
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : Ω → ℝ) (hX : ∀ i, MemLp X 2 (μ i)) (hY : ∀ i, MemLp Y 2 (μ i)) :
    covariance X Y (finiteMixture w μ) =
      (∑ i, (w i : ℝ)*covariance X Y (μ i)) +
      ∑ i, (w i : ℝ)*
        ((∫ ω, X ω ∂μ i)-(∑ j, (w j : ℝ)*∫ ω, X ω ∂μ j))*
        ((∫ ω, Y ω ∂μ i)-(∑ j, (w j : ℝ)*∫ ω, Y ω ∂μ j)) := by
  let M : ℝ := ∑ j, (w j : ℝ)*∫ ω, X ω ∂μ j
  let N : ℝ := ∑ j, (w j : ℝ)*∫ ω, Y ω ∂μ j
  have hx := weighted_integral w μ X (fun i => (hX i).integrable one_le_two)
  have hy := weighted_integral w μ Y (fun i => (hY i).integrable one_le_two)
  rw [covariance, hx, hy]
  rw [weighted_integral w μ (fun ω => (X ω-M)*(Y ω-N))
    (fun i => (hX i |>.sub (memLp_const M)).integrable_mul (hY i |>.sub (memLp_const N)))]
  simp_rw [component_centered_product _ _ _ (hX _) (hY _), mul_add]
  rw [Finset.sum_add_distrib]
  simp only [M, N, mul_assoc]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
def labelLaw (w : ι → ℝ≥0) : Measure ι := finiteMixture w (fun i => Measure.dirac i)

theorem actual_covariance_of_component_means_is_the_between_term
    (w : ι → ℝ≥0) (m n : ι → ℝ) :
    covariance m n (labelLaw w) =
      ∑ i, (w i : ℝ)* (m i-∑ j, (w j : ℝ)*m j)*
        (n i-∑ j, (w j : ℝ)*n j) := by
  have hi (f : ι → ℝ) : (∫ i, f i ∂labelLaw w) = ∑ i, (w i : ℝ)*f i := by
    rw [labelLaw, weighted_integral w (fun i => Measure.dirac i) f
      (fun i => integrable_dirac (by simp))]
    simp
  rw [covariance, hi m, hi n, hi]
  simp only [mul_assoc]

def covarianceMatrix {κ : Type*} (X : κ → Ω → ℝ) (μ : Measure Ω) : Matrix κ κ ℝ :=
  fun a b => covariance (X a) (X b) μ

theorem actual_finite_vector_mixture_covariance_matrix
    {κ : Type*} [Fintype κ] (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : κ → Ω → ℝ) (hX : ∀ a i, MemLp (X a) 2 (μ i)) :
    covarianceMatrix X (finiteMixture w μ) =
      (∑ i, (w i : ℝ) • covarianceMatrix X (μ i)) +
      covarianceMatrix (fun a i => ∫ ω, X a ω ∂μ i) (labelLaw w) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, covarianceMatrix]
  rw [actual_finite_mixture_covariance_within_and_between w hw μ
    (X a) (X b) (hX a) (hX b), actual_covariance_of_component_means_is_the_between_term]
  simp only [smul_eq_mul]

theorem actual_equal_weight_ensemble_covariance_matrix
    {κ : Type*} [Fintype κ] [Nonempty ι]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : κ → Ω → ℝ) (hX : ∀ a i, MemLp (X a) 2 (μ i)) :
    covarianceMatrix X
      (finiteMixture (fun _ => (Fintype.card ι : ℝ≥0)⁻¹) μ) =
      (1/(Fintype.card ι : ℝ)) • (∑ i, covarianceMatrix X (μ i)) +
      covarianceMatrix (fun a i => ∫ ω, X a ω ∂μ i)
        (labelLaw (fun _ => (Fintype.card ι : ℝ≥0)⁻¹)) := by
  have hc : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : (∑ i : ι, (Fintype.card ι : ℝ≥0)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  rw [actual_finite_vector_mixture_covariance_matrix _ hw μ X hX]
  simp only [NNReal.coe_inv, NNReal.coe_natCast, ← Finset.smul_sum, one_div]

end SafeLearning.CompleteAppliedMixtureCovarianceMaterial24
