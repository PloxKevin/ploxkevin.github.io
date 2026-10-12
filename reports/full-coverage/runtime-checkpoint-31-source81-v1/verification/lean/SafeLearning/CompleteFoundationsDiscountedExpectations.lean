import SafeLearning.CompleteFoundationsLessonSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsDiscountedExpectations
open CompleteFoundationsLessonSeries

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def actualDiscountedReturn (gamma : ℝ) (reward : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, gamma^t * reward t ω

def actualExpectedPrefix (gamma : ℝ) (reward : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, gamma^t * ∫ ω, reward t ω ∂μ

theorem actual_each_reward_and_discounted_return_are_genuinely_integrable
    (gamma R : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward : ℕ → Ω → ℝ) (hm : ∀ t, AEStronglyMeasurable (reward t) μ)
    (hr : ∀ t ω, |reward t ω| ≤ R) :
    (∀ t, Integrable (reward t) μ) ∧
      Integrable (actualDiscountedReturn gamma reward) μ := by
  have hint : ∀ t, Integrable (reward t) μ := by
    intro t
    exact (integrable_const R).mono' (hm t)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hr t ω)
  have hmeas : AEStronglyMeasurable (actualDiscountedReturn gamma reward) μ := by
    have hpartial : ∀ T : ℕ, AEStronglyMeasurable
        (fun ω => ∑ t ∈ Finset.range T, gamma^t * reward t ω) μ := by
      intro T
      convert Finset.aestronglyMeasurable_sum (Finset.range T) (fun t _ => (hm t).const_mul (gamma^t)) using 1
      funext ω
      simp only [Finset.sum_apply]
    have hlimit : ∀ᵐ ω ∂μ, Tendsto
        (fun T : ℕ => ∑ t ∈ Finset.range T, gamma^t * reward t ω) atTop
        (𝓝 (actualDiscountedReturn gamma reward ω)) := by
      apply Eventually.of_forall
      intro ω
      exact (actual_bounded_discounted_return_and_tail gamma R (fun t => reward t ω)
        hg0 hg1 (fun t => hr t ω) 0).1.hasSum.tendsto_sum_nat
    exact aestronglyMeasurable_of_tendsto_ae atTop hpartial hlimit
  have hb : ∀ᵐ ω ∂μ, ‖actualDiscountedReturn gamma reward ω‖ ≤ R / (1 - gamma) := by
    apply Eventually.of_forall
    intro ω
    exact (actual_bounded_discounted_return_and_tail gamma R (fun t => reward t ω)
      hg0 hg1 (fun t => hr t ω) 0).2.1
  exact ⟨hint, (integrable_const (R / (1 - gamma))).mono' hmeas hb⟩

theorem actual_discounted_sum_and_expectation_have_a_genuine_hasSum_identity
    (gamma R : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward : ℕ → Ω → ℝ) (hm : ∀ t, AEStronglyMeasurable (reward t) μ)
    (hr : ∀ t ω, |reward t ω| ≤ R) :
    HasSum (fun t => gamma^t * ∫ ω, reward t ω ∂μ)
      (∫ ω, actualDiscountedReturn gamma reward ω ∂μ) := by
  have hgeom : Summable (fun t : ℕ => gamma^t) :=
    summable_geometric_of_lt_one hg0 hg1
  have h := hasSum_integral_of_dominated_convergence
    (fun t (_ω : Ω) => gamma^t * R)
    (fun t => (hm t).const_mul (gamma^t))
    (fun t => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun _ω => hgeom.mul_right R)
    (integrable_const (∑' t : ℕ, gamma^t * R))
    (Eventually.of_forall fun ω =>
      (actual_bounded_discounted_return_and_tail gamma R (fun t => reward t ω)
        hg0 hg1 (fun t => hr t ω) 0).1.hasSum)
  · simpa only [integral_const_mul, actualDiscountedReturn] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hg0 t)]
    exact mul_le_mul_of_nonneg_left (hr t ω) (pow_nonneg hg0 t)

theorem actual_expected_discounted_return_has_the_literal_sum_expectation_identity
    (gamma R : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward : ℕ → Ω → ℝ) (hm : ∀ t, AEStronglyMeasurable (reward t) μ)
    (hr : ∀ t ω, |reward t ω| ≤ R) :
    (∫ ω, actualDiscountedReturn gamma reward ω ∂μ) =
      ∑' t, gamma^t * ∫ ω, reward t ω ∂μ := by
  exact (actual_discounted_sum_and_expectation_have_a_genuine_hasSum_identity μ
    gamma R hg0 hg1 reward hm hr).tsum_eq.symm

theorem actual_geometric_tail_bounds_every_expected_discounted_prefix_error
    (gamma R : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward : ℕ → Ω → ℝ) (hm : ∀ t, AEStronglyMeasurable (reward t) μ)
    (hr : ∀ t ω, |reward t ω| ≤ R) (T : ℕ) :
    |(∫ ω, actualDiscountedReturn gamma reward ω ∂μ) - actualExpectedPrefix μ gamma reward T| ≤
      gamma^T * R / (1 - gamma) := by
  have he : ∀ t, |∫ ω, reward t ω ∂μ| ≤ R := by
    intro t
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := reward t) (C := R)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hr t ω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hs := actual_discounted_sum_and_expectation_have_a_genuine_hasSum_identity μ
    gamma R hg0 hg1 reward hm hr
  have hid := hs.summable.sum_add_tsum_nat_add T
  have hsum := hs.tsum_eq
  have htail := (actual_bounded_discounted_return_and_tail gamma R
    (fun t => ∫ ω, reward t ω ∂μ) hg0 hg1 he T).2.2
  have hdiff : (∫ ω, actualDiscountedReturn gamma reward ω ∂μ) - actualExpectedPrefix μ gamma reward T =
      ∑' t : ℕ, gamma^(t + T) * ∫ ω, reward (t + T) ω ∂μ := by
    unfold actualExpectedPrefix
    rw [← hsum]
    linarith [hid]
  rw [hdiff]
  exact htail

theorem actual_expected_discounted_prefix_error_tends_to_zero
    (gamma R : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (reward : ℕ → Ω → ℝ) (hm : ∀ t, AEStronglyMeasurable (reward t) μ)
    (hr : ∀ t ω, |reward t ω| ≤ R) :
    Tendsto (fun T => |(∫ ω, actualDiscountedReturn gamma reward ω ∂μ) - actualExpectedPrefix μ gamma reward T|)
      atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hg0 hg1).mul_const (R / (1 - gamma))
  apply squeeze_zero (fun _ => abs_nonneg _) (fun T => ?_)
  · simpa only [zero_mul] using ht
  · simpa only [mul_div_assoc] using
      actual_geometric_tail_bounds_every_expected_discounted_prefix_error μ gamma R hg0 hg1 reward hm hr T

end SafeLearning.CompleteFoundationsDiscountedExpectations
