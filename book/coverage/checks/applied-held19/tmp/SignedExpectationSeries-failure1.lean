import SafeLearning.CompleteFoundationsDiscountedExpectations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
namespace SafeLearning.CompleteAppliedSignedExpectationSeries

variable {Omega : Type*} [MeasurableSpace Omega]

theorem actual_finite_absolute_expectation_series_derives_all_stage_integrability
    (P : Measure Omega) (X : ℕ → Omega → ℝ)
    (hm : ∀ t,AEStronglyMeasurable (X t) P)
    (hb : (∑' t,∫⁻ o,‖X t o‖ₑ ∂P)<⊤) :
    ∀ t,Integrable (X t) P := by
  intro t
  refine ⟨hm t,?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  exact lt_of_le_of_lt (ENNReal.le_tsum t) hb

theorem actual_finite_absolute_expectation_series_derives_absolute_path_summability
    (P : Measure Omega) (X : ℕ → Omega → ℝ)
    (hm : ∀ t,AEStronglyMeasurable (X t) P)
    (hb : (∑' t,∫⁻ o,‖X t o‖ₑ ∂P)<⊤) :
    ∀ᵐ o ∂P,Summable (fun t => |X t o|) ∧ Summable (fun t => X t o) := by
  have he : (∫⁻ o,∑' t,‖X t o‖ₑ ∂P)<⊤ := by
    rw [lintegral_tsum (fun t => (hm t).enorm)]
    exact hb
  have ha := ae_lt_top' (AEMeasurable.tsum (fun t => (hm t).enorm)) he.ne
  filter_upwards [ha] with o ho
  have hs : Summable (fun t => (‖X t o‖₊:ℝ)) := by
    rw [←ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact ho.ne
  have hnorm : Summable (fun t => ‖X t o‖) := hs
  exact ⟨by simpa only [Real.norm_eq_abs] using hnorm,hnorm.of_norm⟩

theorem actual_finite_absolute_expectation_series_derives_integrable_signed_return
    (P : Measure Omega) (X : ℕ → Omega → ℝ)
    (hm : ∀ t,AEStronglyMeasurable (X t) P)
    (hb : (∑' t,∫⁻ o,‖X t o‖ₑ ∂P)<⊤) :
    Integrable (fun o => ∑' t,X t o) P := by
  have hs := actual_finite_absolute_expectation_series_derives_absolute_path_summability P X hm hb
  have hp : ∀ T : ℕ,AEStronglyMeasurable (fun o => ∑ t∈Finset.range T,X t o) P := by
    intro T
    convert Finset.aestronglyMeasurable_sum (Finset.range T) (fun t _ => hm t) using 1
    funext o
    simp only [Finset.sum_apply]
  have hl : ∀ᵐ o ∂P,Tendsto (fun T => ∑ t∈Finset.range T,X t o) atTop (𝓝 (∑' t,X t o)) := by
    filter_upwards [hs] with o ho
    exact ho.2.hasSum.tendsto_sum_nat
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hp hl,?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  calc
    (∫⁻ o,‖∑' t,X t o‖ₑ ∂P) ≤ ∫⁻ o,∑' t,‖X t o‖ₑ ∂P :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' t,∫⁻ o,‖X t o‖ₑ ∂P := lintegral_tsum (fun t => (hm t).enorm)
    _ < ⊤ := hb

theorem actual_signed_sum_expectation_exchange_has_the_genuine_absolute_finiteness_domain
    (P : Measure Omega) (X : ℕ → Omega → ℝ)
    (hm : ∀ t,AEStronglyMeasurable (X t) P)
    (hb : (∑' t,∫⁻ o,ENNReal.ofReal |X t o| ∂P)<⊤) :
    (∀ t,Integrable (X t) P) ∧ Integrable (fun o => ∑' t,X t o) P ∧
      (∀ᵐ o ∂P,Summable (fun t => |X t o|) ∧ Summable (fun t => X t o)) ∧
      (∫ o,∑' t,X t o ∂P)=∑' t,∫ o,X t o ∂P := by
  have hb' : (∑' t,∫⁻ o,‖X t o‖ₑ ∂P)<⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using hb
  exact ⟨actual_finite_absolute_expectation_series_derives_all_stage_integrability P X hm hb',
    actual_finite_absolute_expectation_series_derives_integrable_signed_return P X hm hb',
    actual_finite_absolute_expectation_series_derives_absolute_path_summability P X hm hb',
    integral_tsum hm hb'.ne⟩

theorem actual_discounted_expected_absolute_series_has_the_literal_geometric_bound
    (P : Measure Omega) [IsProbabilityMeasure P]
    (gamma R : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1)
    (reward : ℕ → Omega → ℝ) (hm : ∀ t,AEStronglyMeasurable (reward t) P)
    (hr : ∀ t o,|reward t o|≤R) :
    Summable (fun t => gamma^t*∫ o,|reward t o| ∂P) ∧
      (∑' t,gamma^t*∫ o,|reward t o| ∂P)≤R/(1-gamma) := by
  have hi := (CompleteFoundationsDiscountedExpectations.actual_each_reward_and_discounted_return_are_genuinely_integrable
    P gamma R hg0 hg1 reward hm hr).1
  have hstage : ∀ t,(∫ o,|reward t o| ∂P)≤R := by
    intro t
    have he := integral_mono_ae (hi t).abs (integrable_const R)
      (Filter.Eventually.of_forall (hr t))
    simpa only [integral_const,probReal_univ,one_smul] using he
  have hg := (summable_geometric_of_lt_one hg0 hg1).mul_right R
  have hn : ∀ t,0≤gamma^t*∫ o,|reward t o| ∂P := fun t =>
    mul_nonneg (pow_nonneg hg0 t) (integral_nonneg (fun _ => abs_nonneg _))
  have hu : ∀ t,gamma^t*∫ o,|reward t o| ∂P≤gamma^t*R := fun t =>
    mul_le_mul_of_nonneg_left (hstage t) (pow_nonneg hg0 t)
  have hs := Summable.of_nonneg_of_le hn hu hg
  refine ⟨hs,?_⟩
  calc
    (∑' t,gamma^t*∫ o,|reward t o| ∂P) ≤ ∑' t,gamma^t*R := hs.tsum_le_tsum hu hg
    _ = R/(1-gamma) := by
      rw [tsum_mul_right,tsum_geometric_of_lt_one hg0 hg1]
      ring

end SafeLearning.CompleteAppliedSignedExpectationSeries
