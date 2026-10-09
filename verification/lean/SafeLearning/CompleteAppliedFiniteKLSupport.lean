import SafeLearning.CompleteAppliedFiniteKL
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteKLSupport
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedFiniteKL
open scoped ENNReal NNReal Classical

theorem actual_support_density {n : ℕ} (p q : PMF (Fin n))
    (hs : ∀ i,p i≠0 → q i≠0) :
    p.toMeasure=q.toMeasure.withDensity (fun i => p i/q i) := by
  apply Measure.ext_of_singleton
  intro i
  rw [withDensity_apply _ (measurableSet_singleton i),lintegral_singleton,
    PMF.toMeasure_apply_singleton p i (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton q i (measurableSet_singleton i)]
  by_cases hq:q i=0
  · have hp:p i=0 := by by_contra hn;exact hs i hn hq
    simp [hp,hq]
  · exact (ENNReal.div_mul_cancel hq (q.apply_ne_top i)).symm

theorem actual_support_absolute_continuity {n : ℕ} (p q : PMF (Fin n)) :
    p.toMeasure≪q.toMeasure ↔ ∀ i,p i≠0 → q i≠0 := by
  constructor
  · intro h i hp hq
    have hz:q.toMeasure {i}=0 := by
      rw [PMF.toMeasure_apply_singleton q i (measurableSet_singleton i),hq]
    have hx:=h hz
    rw [PMF.toMeasure_apply_singleton p i (measurableSet_singleton i)] at hx
    exact hp hx
  · intro hs
    rw [actual_support_density p q hs]
    exact withDensity_absolutelyContinuous _ _

theorem actual_support_kl_sum {n : ℕ} (p q : PMF (Fin n))
    (hs : ∀ i,p i≠0 → q i≠0) :
    (klDiv p.toMeasure q.toMeasure).toReal=
      ∑ i,(p i).toReal*Real.log ((p i).toReal/(q i).toReal) := by
  have hac:=(actual_support_absolute_continuity p q).mpr hs
  have hr:p.toMeasure.rnDeriv q.toMeasure=ᵐ[q.toMeasure] (fun i=>p i/q i) := by
    rw [actual_support_density p q hs]
    exact Measure.rnDeriv_withDensity _ (measurable_of_finite _)
  have he:(∫ i,llr p.toMeasure q.toMeasure i ∂p.toMeasure)=
      ∫ i,Real.log ((p i).toReal/(q i).toReal) ∂p.toMeasure := by
    apply integral_congr_ae
    filter_upwards [hac.ae_le hr] with i hi
    simp only [llr,hi,ENNReal.toReal_div]
  rw [toReal_klDiv hac Integrable.of_finite,probReal_univ,probReal_univ,
    add_sub_cancel_right,he,PMF.integral_eq_sum]
  rfl

theorem actual_support_kl_full_definition {n : ℕ} (p q : PMF (Fin n)) :
    klDiv p.toMeasure q.toMeasure=
      if ∀ i,p i≠0 → q i≠0 then
        ENNReal.ofReal (∑ i,(p i).toReal*Real.log ((p i).toReal/(q i).toReal)) else ⊤ := by
  split_ifs with hs
  · have hac:=(actual_support_absolute_continuity p q).mpr hs
    calc
      _=ENNReal.ofReal (klDiv p.toMeasure q.toMeasure).toReal :=
        (ENNReal.ofReal_toReal (klDiv_ne_top hac Integrable.of_finite)).symm
      _=_ := congrArg ENNReal.ofReal (actual_support_kl_sum p q hs)
  · exact klDiv_of_not_ac (by rwa [actual_support_absolute_continuity p q])

theorem actual_finite_gibbs_nonnegative {n : ℕ} (p q : PMF (Fin n))
    (hs : ∀ i,p i≠0 → q i≠0) :
    0≤∑ i,(p i).toReal*Real.log ((p i).toReal/(q i).toReal) := by
  rw [← actual_support_kl_sum p q hs]
  exact ENNReal.toReal_nonneg

theorem actual_finite_gibbs_equality {n : ℕ} (p q : PMF (Fin n)) :
    klDiv p.toMeasure q.toMeasure=0 ↔ p=q := by
  rw [klDiv_eq_zero_iff,PMF.toMeasure_injective.eq_iff]

theorem actual_zero_weight_log_convention (q : ℝ) : (0:ℝ)*Real.log (0/q)=0 := by simp

end SafeLearning.CompleteAppliedFiniteKLSupport
