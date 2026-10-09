import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedReturns
open MeasureTheory

/-- Bounded rewards justify interchanging expectation and the infinite discounted sum.
No independence between different time steps is required. -/
theorem discounted_expectation_interchange {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (gamma bound : ℝ)
    (hg : |gamma| < 1) (hm : ∀ n, AEStronglyMeasurable (X n) μ)
    (hb : ∀ n, ∀ᵐ omega ∂μ, |X n omega| ≤ bound) :
    (∫ omega, ∑' n : ℕ, gamma^n*X n omega ∂μ)=
      ∑' n : ℕ, gamma^n*(∫ omega, X n omega ∂μ) := by
  have hint : ∀ n, Integrable (X n) μ := by
    intro n; apply Integrable.of_bound (hm n) bound
    simpa only [Real.norm_eq_abs] using hb n
  have hdisc : ∀ n, Integrable (fun omega => gamma^n*X n omega) μ :=
    fun n => (hint n).const_mul _
  have hgeom : Summable (fun n : ℕ => |gamma|^n*bound) :=
    (summable_geometric_of_abs_lt_one (by simpa only [abs_abs] using hg)).mul_right bound
  have hnorm : Summable (fun n : ℕ => ∫ omega, ‖gamma^n*X n omega‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun omega => norm_nonneg _)) ?_ hgeom
    intro n
    have hh := integral_mono_ae (hdisc n).norm (integrable_const (|gamma|^n*bound)) (by
      filter_upwards [hb n] with omega h
      simp only [Real.norm_eq_abs,abs_mul,abs_pow]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg gamma) n))
    simpa using hh
  rw [← integral_tsum_of_summable_integral_norm hdisc hnorm]
  simp_rw [integral_const_mul]

end SafeLearning.CompleteAppliedReturns
