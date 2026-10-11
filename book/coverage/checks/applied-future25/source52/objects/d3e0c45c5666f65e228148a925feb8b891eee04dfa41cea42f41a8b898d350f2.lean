import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Function
namespace SafeLearning.CompleteAppliedTruncatedConditioningMaterial25

theorem actual_conditioning_has_the_cut_and_normalized_density
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (p : α → ℝ≥0∞)
    (hp : Measurable p) (A : Set α) (hA : MeasurableSet A) :
    (ν.withDensity p)[|A] = ν.withDensity
      (fun x => p x * A.indicator (fun _ => (1 : ℝ≥0∞)) x / (ν.withDensity p) A) := by
  have hf : (fun x => p x * A.indicator (fun _ => (1 : ℝ≥0∞)) x /
      (ν.withDensity p) A) = ((ν.withDensity p) A)⁻¹ • A.indicator p := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, div_eq_mul_inv, mul_comm]
  rw [hf, Measure.withDensity_smul _ (hp.indicator hA),
    Measure.withDensity_indicator hA, ← Measure.restrict_withDensity hA]
  rfl

theorem actual_random_variable_conditioning_pushes_forward_to_its_conditional_law
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X)
    (A : Set α) (hA : MeasurableSet A) :
    (μ[|X ⁻¹' A]).map X = (μ.map X)[|A] := by
  change ((μ (X ⁻¹' A))⁻¹ • μ.restrict (X ⁻¹' A)).map X =
    ((μ.map X) A)⁻¹ • (μ.map X).restrict A
  rw [Measure.map_smul _ hX.aemeasurable,
    ← Measure.restrict_map hX hA, Measure.map_apply hX hA]

theorem actual_positive_density_region_gives_a_true_normalized_conditional_law
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (p : α → ℝ≥0∞)
    (hp : Measurable p) [IsProbabilityMeasure (ν.withDensity p)]
    (A : Set α) (hA : MeasurableSet A) (hc : 0 < (ν.withDensity p).real A) :
    IsProbabilityMeasure (ν.withDensity
      (fun x => p x * A.indicator (fun _ => (1 : ℝ≥0∞)) x / (ν.withDensity p) A)) ∧
      (∀ᵐ x ∂(ν.withDensity p)[|A], x ∈ A) := by
  have hn : (ν.withDensity p) A ≠ 0 := by
    intro hz
    have : (ν.withDensity p).real A = 0 := by simp [measureReal_def, hz]
    linarith
  rw [← actual_conditioning_has_the_cut_and_normalized_density ν p hp A hA]
  exact ⟨cond_isProbabilityMeasure hn, ae_cond_mem hA⟩

theorem actual_nested_conditional_bounds_need_no_independence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S A : Set Ω) (hA : MeasurableSet A) (p c : ℝ)
    (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hcond : p ≤ (μ[|A]).real S) (hmass : c ≤ μ.real A) :
    p * c ≤ μ.real (S ∩ A) ∧ p * c ≤ μ.real S := by
  have hprod : (μ[|A]).real S * μ.real A = μ.real (S ∩ A) := by
    have h := congrArg ENNReal.toReal (cond_mul_eq_inter hA S μ)
    simpa only [ENNReal.toReal_mul, ← measureReal_def, inter_comm A S] using h
  have h : p * c ≤ μ.real (S ∩ A) := by
    rw [← hprod]
    exact mul_le_mul hcond hmass hc (measureReal_nonneg _ _)
  exact ⟨h, h.trans (measureReal_mono inter_subset_left)⟩

theorem actual_literal_truncated_stability_lower_bound_is_9405_over_10000
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S A : Set Ω) (hA : MeasurableSet A)
    (hcond : (95 : ℝ) / 100 ≤ (μ[|A]).real S)
    (hmass : (99 : ℝ) / 100 ≤ μ.real A) :
    (9405 : ℝ) / 10000 ≤ μ.real S := by
  have h := (actual_nested_conditional_bounds_need_no_independence μ S A hA
    (95/100) (99/100) (by norm_num) (by norm_num) hcond hmass).2
  norm_num at h ⊢
  exact h

theorem actual_hyperparameter_and_function_bounds_have_product_and_union_floor
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B F : Set Ω) (hB : MeasurableSet B) (δ₁ δ₂ : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hu₁ : δ₁ ≤ 1) (hu₂ : δ₂ ≤ 1)
    (hbox : 1-δ₁ ≤ μ.real B) (hband : 1-δ₂ ≤ (μ[|B]).real F) :
    (1-δ₁)*(1-δ₂) ≤ μ.real (B ∩ F) ∧
      1-δ₁-δ₂ ≤ μ.real (B ∩ F) := by
  have h := (actual_nested_conditional_bounds_need_no_independence μ F B hB
    (1-δ₂) (1-δ₁) (by linarith) (by linarith) hband hbox).1
  have hprod : (1-δ₁)*(1-δ₂) ≤ μ.real (B ∩ F) := by
    simpa only [inter_comm F B, mul_comm (1-δ₂) (1-δ₁)] using h
  refine ⟨hprod, le_trans ?_ hprod⟩
  nlinarith [mul_nonneg hδ₁ hδ₂]

theorem actual_calibration_conditional_coverage_averages_to_marginal_coverage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (Y : Ω → α) (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)]
    (S : Set Ω) (hS : MeasurableSet S) :
    (∫ ω, (μ[(S.indicator fun _ => (1 : ℝ)) | MeasurableSpace.comap Y inferInstance]) ω ∂μ)
      = μ.real S := by
  exact integral_condExp_indicator hY hS

end SafeLearning.CompleteAppliedTruncatedConditioningMaterial25
