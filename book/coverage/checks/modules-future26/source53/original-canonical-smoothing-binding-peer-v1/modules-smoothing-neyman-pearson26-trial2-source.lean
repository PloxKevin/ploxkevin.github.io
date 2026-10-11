import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesSmoothingNeymanPearson26

variable {E : Type*} [MeasurableSpace E]

theorem actual_density_test_transfer_from_low_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, q z ≤ cutoff * p z)
    (houtside : ∀ z ∉ S, cutoff * p z ≤ q z)
    (hmass : (∫ z in S, p z ∂base) ≤ ∫ z, h z * p z ∂base) :
    (∫ z in S, q z ∂base) ≤ ∫ z, h z * q z ∂base := by
  have hpoint (z : E) :
      cutoff * (h z * p z - S.indicator p z) ≤ h z * q z - S.indicator q z := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (cutoff*p z-q z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      exact (by nlinarith [mul_nonneg ((hh z).1)
        (sub_nonneg.mpr (houtside z hz))])
  have hi := integral_mono ((hhp.sub (hp.indicator hS)).const_mul cutoff)
    (hhq.sub (hq.indicator hS)) hpoint
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_density_test_transfer_from_high_likelihood_region
    (base : Measure E) (p q h : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hp : Integrable p base) (hq : Integrable q base)
    (hhp : Integrable (fun z => h z * p z) base)
    (hhq : Integrable (fun z => h z * q z) base)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (cutoff : ℝ) (ht : 0 ≤ cutoff)
    (hinside : ∀ z ∈ S, cutoff * p z ≤ q z)
    (houtside : ∀ z ∉ S, q z ≤ cutoff * p z)
    (hmass : (∫ z, h z * p z ∂base) ≤ ∫ z in S, p z ∂base) :
    (∫ z, h z * q z ∂base) ≤ ∫ z in S, q z ∂base := by
  have hpoint (z : E) :
      h z * q z - S.indicator q z ≤ cutoff * (h z * p z - S.indicator p z) := by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      have hn : 0 ≤ (1-h z) * (q z-cutoff*p z) :=
        mul_nonneg (sub_nonneg.mpr (hh z).2) (sub_nonneg.mpr (hinside z hz))
      nlinarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]
      exact (by nlinarith [mul_nonneg ((hh z).1)
        (sub_nonneg.mpr (houtside z hz))])
  have hi := integral_mono (hhq.sub (hq.indicator hS))
    ((hhp.sub (hp.indicator hS)).const_mul cutoff) hpoint
  rw [integral_const_mul,integral_sub hhp (hp.indicator hS),
    integral_sub hhq (hq.indicator hS),integral_indicator hS,integral_indicator hS] at hi
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmass)]

theorem actual_bounded_measurable_test_has_integrable_density_products
    (base : Measure E) (p h : E → ℝ) (hp : Integrable p base)
    (hm : Measurable h) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ 1) :
    Integrable (fun z => h z * p z) base := by
  apply hp.bdd_mul hm.aestronglyMeasurable
  exact ae_of_all base (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hh z).1]
    exact (hh z).2)

end SafeLearning.CompleteModulesSmoothingNeymanPearson26
