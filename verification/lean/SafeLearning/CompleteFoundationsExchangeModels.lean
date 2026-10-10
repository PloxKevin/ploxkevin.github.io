import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace SafeLearning.CompleteFoundationsExchangeModels

def movingMass (n t : ℕ) : ℝ := if t = n then 1 else 0

theorem actual_moving_mass_is_nonnegative (n t : ℕ) : 0 ≤ movingMass n t := by
  unfold movingMass
  split_ifs <;> norm_num

theorem actual_each_moving_mass_row_has_sum_one (n : ℕ) :
    HasSum (movingMass n) 1 := by
  change HasSum (fun t : ℕ => if t = n then (1 : ℝ) else 0) 1
  exact hasSum_ite_eq n (1 : ℝ)

theorem actual_each_fixed_moving_mass_column_tends_to_zero (t : ℕ) :
    Tendsto (fun n => movingMass n t) atTop (𝓝 0) := by
  have hzero : ∀ᶠ n : ℕ in atTop, movingMass n t = 0 := by
    apply eventually_atTop.2
    refine ⟨t + 1, ?_⟩
    intro n hn
    have hne : t ≠ n := by omega
    simp [movingMass, hne]
  exact tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)

theorem actual_nonnegative_moving_mass_limit_and_sum_cannot_be_exchanged :
    (∀ n t, 0 ≤ movingMass n t) ∧
    Tendsto (fun n => ∑' t, movingMass n t) atTop (𝓝 1) ∧
    (∀ t, Tendsto (fun n => movingMass n t) atTop (𝓝 0)) ∧
    (∑' _t : ℕ, (0 : ℝ)) = 0 ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨actual_moving_mass_is_nonnegative, ?_,
    actual_each_fixed_moving_mass_column_tends_to_zero, by simp, by norm_num⟩
  have heq : (fun n => ∑' t, movingMass n t) = fun _ : ℕ => (1 : ℝ) := by
    funext n
    exact (actual_each_moving_mass_row_has_sum_one n).tsum_eq
  rw [heq]
  exact tendsto_const_nhds

/-- Nonnegative sums may take the value infinity; no finite-real coercion is made. -/
theorem actual_nonnegative_double_sums_can_be_exchanged (a : ℕ → ℕ → ℝ≥0∞) :
    (∑' n, ∑' t, a n t) = ∑' t, ∑' n, a n t := ENNReal.tsum_comm

theorem actual_nonnegative_sum_and_expectation_can_be_exchanged
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ t, AEMeasurable (X t) μ) :
    (∫⁻ ω, ∑' t, X t ω ∂μ) = ∑' t, ∫⁻ ω, X t ω ∂μ :=
  lintegral_tsum hX

theorem actual_summable_domination_gives_summable_rows_limit_and_exchange
    (a : ℕ → ℕ → ℝ) (limit bound : ℕ → ℝ)
    (hb : Summable bound)
    (ha : ∀ n t, |a n t| ≤ bound t)
    (hl : ∀ t, Tendsto (fun n => a n t) atTop (𝓝 (limit t))) :
    (∀ n, Summable (a n)) ∧ Summable limit ∧
      Tendsto (fun n => ∑' t, a n t) atTop (𝓝 (∑' t, limit t)) := by
  have hab : ∀ n t, ‖a n t‖ ≤ bound t := by simpa only [Real.norm_eq_abs] using ha
  have hlb : ∀ t, ‖limit t‖ ≤ bound t := by
    intro t
    exact le_of_tendsto (tendsto_norm.comp (hl t)) (Eventually.of_forall fun n => hab n t)
  refine ⟨fun n => hb.of_norm_bounded (hab n), hb.of_norm_bounded hlb, ?_⟩
  exact tendsto_tsum_of_dominated_convergence hb hl (Eventually.of_forall hab)

theorem actual_dominated_convergence_derives_integrability_and_expectation_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (limit Z : Ω → ℝ)
    (hY : ∀ n, AEStronglyMeasurable (Y n) μ) (hZ : Integrable Z μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ Z ω)
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (limit ω))) :
    (∀ n, Integrable (Y n) μ) ∧ Integrable limit μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop (𝓝 (∫ ω, limit ω ∂μ)) := by
  have hb' : ∀ n, ∀ᵐ ω ∂μ, ‖Y n ω‖ ≤ Z ω := by simpa only [Real.norm_eq_abs] using hb
  have hm : AEStronglyMeasurable limit μ := aestronglyMeasurable_of_tendsto_ae atTop hY hl
  have hlimit : ∀ᵐ ω ∂μ, ‖limit ω‖ ≤ Z ω := by
    filter_upwards [hl, ae_all_iff.2 hb'] with ω hω hbound
    exact le_of_tendsto (tendsto_norm.comp hω) (Eventually.of_forall hbound)
  exact ⟨fun n => hZ.mono' (hY n) (hb' n), hZ.mono' hm hlimit,
    tendsto_integral_of_dominated_convergence Z hY hZ hb' hl⟩

theorem actual_bounded_convergence_on_a_probability_space
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (limit : Ω → ℝ) (C : ℝ)
    (hY : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ C)
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (limit ω))) :
    (∀ n, Integrable (Y n) μ) ∧ Integrable limit μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop (𝓝 (∫ ω, limit ω ∂μ)) := by
  exact actual_dominated_convergence_derives_integrability_and_expectation_limit μ Y limit
    (fun _ => C) hY (integrable_const C) hb hl

theorem actual_monotone_nonnegative_expectations_converge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) (limit : Ω → ℝ≥0∞)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hm : ∀ᵐ ω ∂μ, Monotone (fun n => Y n ω))
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (limit ω))) :
    Tendsto (fun n => ∫⁻ ω, Y n ω ∂μ) atTop (𝓝 (∫⁻ ω, limit ω ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone hY hm hl

theorem actual_monotone_nonnegative_sums_converge
    (a : ℕ → ℕ → ℝ≥0∞) (limit : ℕ → ℝ≥0∞)
    (hm : ∀ t, Monotone (fun n => a n t))
    (hl : ∀ t, Tendsto (fun n => a n t) atTop (𝓝 (limit t))) :
    Tendsto (fun n => ∑' t, a n t) atTop (𝓝 (∑' t, limit t)) := by
  have h := actual_monotone_nonnegative_expectations_converge
    (Measure.count : Measure ℕ) a limit
    (fun _ => (measurable_of_countable _).aemeasurable)
    (Eventually.of_forall hm) (Eventually.of_forall hl)
  simpa only [lintegral_count] using h

end SafeLearning.CompleteFoundationsExchangeModels
