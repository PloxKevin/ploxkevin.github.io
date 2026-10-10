import SafeLearning.CompleteAppliedTwoAtomRisk
import Mathlib.InformationTheory.KullbackLeibler.Basic
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteKL
open MeasureTheory InformationTheory
open scoped ENNReal NNReal

theorem actual_finite_density {n : ℕ} (p q : PMF (Fin n)) (hq : ∀ i,q i≠0) :
    p.toMeasure=q.toMeasure.withDensity (fun i => p i/q i) := by
  apply Measure.ext_of_singleton
  intro i
  rw [withDensity_apply _ (measurableSet_singleton i),lintegral_singleton,
    PMF.toMeasure_apply_singleton p i (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton q i (measurableSet_singleton i)]
  exact (ENNReal.div_mul_cancel (hq i) (q.apply_ne_top i)).symm

theorem actual_finite_absolute_continuity {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) : p.toMeasure≪q.toMeasure := by
  rw [actual_finite_density p q hq]
  exact withDensity_absolutelyContinuous _ _

theorem actual_finite_rn_derivative {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) : p.toMeasure.rnDeriv q.toMeasure=ᵐ[q.toMeasure] (fun i => p i/q i) := by
  rw [actual_finite_density p q hq]
  exact Measure.rnDeriv_withDensity _ (measurable_of_finite _)

theorem actual_finite_kl_integral {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) :
    (klDiv p.toMeasure q.toMeasure).toReal=
      ∫ i,Real.log ((p i).toReal/(q i).toReal) ∂p.toMeasure := by
  have hac:=actual_finite_absolute_continuity p q hq
  rw [toReal_klDiv hac (Integrable.of_finite),probReal_univ,probReal_univ,add_sub_cancel_right]
  apply integral_congr_ae
  have hr:=hac.ae_le (actual_finite_rn_derivative p q hq)
  filter_upwards [hr] with i hi
  simp only [llr,hi,ENNReal.toReal_div]

theorem actual_finite_kl_sum {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) :
    (klDiv p.toMeasure q.toMeasure).toReal=
      ∑ i,(p i).toReal*Real.log ((p i).toReal/(q i).toReal) := by
  rw [actual_finite_kl_integral p q hq,PMF.integral_eq_sum]
  rfl

theorem actual_finite_kl_is_finite {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) : klDiv p.toMeasure q.toMeasure≠⊤ :=
  klDiv_ne_top (actual_finite_absolute_continuity p q hq) Integrable.of_finite

theorem actual_missing_support_infinite_kl {n : ℕ} (p q : PMF (Fin n))
    (i : Fin n) (hp : p i≠0) (hq : q i=0) : klDiv p.toMeasure q.toMeasure=⊤ := by
  apply klDiv_of_not_ac
  intro hac
  have he:q.toMeasure {i}=0 := by
    rw [PMF.toMeasure_apply_singleton q i (measurableSet_singleton i),hq]
  have hd:=hac he
  rw [PMF.toMeasure_apply_singleton p i (measurableSet_singleton i)] at hd
  exact hp hd

end SafeLearning.CompleteAppliedFiniteKL
