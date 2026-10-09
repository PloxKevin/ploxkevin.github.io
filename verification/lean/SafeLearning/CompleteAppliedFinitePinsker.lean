import SafeLearning.CompleteAppliedBinaryPinsker
import SafeLearning.CompleteAppliedFiniteVariation
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFinitePinsker
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteVariation
open SafeLearning.CompleteAppliedTwoAtomRisk SafeLearning.CompleteAppliedBinaryPinsker
open scoped ENNReal NNReal Classical

def eventParameter {n : ℕ} (p : PMF (Fin n)) (E : Set (Fin n)) : unitInterval :=
  ⟨p.toMeasure.real E,measureReal_nonneg,measureReal_le_one⟩
def eventIndicator {n : ℕ} (E : Set (Fin n)) (i : Fin n) : Fin 2 := if i∈E then 1 else 0

theorem actual_event_indicator_law {n : ℕ} (p : PMF (Fin n)) (E : Set (Fin n)) :
    p.toMeasure.map (eventIndicator E)=(costLaw (eventParameter p E)).toMeasure := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  fin_cases k
  · change p.toMeasure (eventIndicator E ⁻¹' {(0:Fin 2)})=(costLaw (eventParameter p E)) 0
    have he:eventIndicator E ⁻¹' {(0:Fin 2)}=Eᶜ := by
      ext i
      by_cases h:i∈E <;> simp [eventIndicator,h]
    rw [he]
    change p.toMeasure Eᶜ=ENNReal.ofReal (1-p.toMeasure.real E)
    rw [← probReal_compl_eq_one_sub (Set.toFinite E).measurableSet]
    exact (ENNReal.ofReal_toReal (by finiteness)).symm
  · change p.toMeasure (eventIndicator E ⁻¹' {(1:Fin 2)})=(costLaw (eventParameter p E)) 1
    have he:eventIndicator E ⁻¹' {(1:Fin 2)}=E := by
      ext i
      by_cases h:i∈E <;> simp [eventIndicator,h]
    rw [he]
    change p.toMeasure E=ENNReal.ofReal (p.toMeasure E).toReal
    exact (ENNReal.ofReal_toReal (by finiteness)).symm

theorem actual_finite_tv_has_attaining_event {n : ℕ} (p q : PMF (Fin n)) :
    ∃ E : Set (Fin n),totalVariation p q=|p.toMeasure.real E-q.toMeasure.real E| := by
  let f:Set (Fin n)→ℝ:=fun E=>|p.toMeasure.real E-q.toMeasure.real E|
  have he:{d | ∃ E : Set (Fin n),d=|p.toMeasure.real E-q.toMeasure.real E|}=Set.range f := by
    ext d
    simp only [Set.mem_setOf_eq,Set.mem_range]
    constructor
    · rintro ⟨E,h⟩
      exact ⟨E,h.symm⟩
    · rintro ⟨E,h⟩
      exact ⟨E,h.symm⟩
  have hm: sSup (Set.range f)∈Set.range f :=
    (Set.range_nonempty f).csSup_mem (Set.finite_range f)
  obtain ⟨E,hE⟩:=hm
  exact ⟨E,by unfold totalVariation;rw [he];exact hE.symm⟩

/-- Genuine finite-distribution Pinsker, including infinite divergence at missing support. -/
theorem actual_finite_pinsker_squared {n : ℕ} (p q : PMF (Fin n)) :
    ENNReal.ofReal (2*totalVariation p q^2)≤klDiv p.toMeasure q.toMeasure := by
  obtain ⟨E,hE⟩:=actual_finite_tv_has_attaining_event p q
  have hp:=actual_binary_pinsker (eventParameter p E) (eventParameter q E)
  have htv:totalVariation (costLaw (eventParameter p E)) (costLaw (eventParameter q E))=
      totalVariation p q := by
    rw [actual_binary_total_variation,hE]
    rfl
  rw [htv] at hp
  apply hp.trans
  rw [← actual_event_indicator_law,← actual_event_indicator_law]
  exact klDiv_map_le _ _ (measurable_of_finite _)

theorem actual_finite_pinsker_finite_real {n : ℕ} (p q : PMF (Fin n))
    (hfinite : klDiv p.toMeasure q.toMeasure≠⊤) :
    totalVariation p q≤Real.sqrt ((klDiv p.toMeasure q.toMeasure).toReal/2) := by
  have hs:=actual_finite_pinsker_squared p q
  have hr:2*totalVariation p q^2≤(klDiv p.toMeasure q.toMeasure).toReal := by
    have ht: (ENNReal.ofReal (2*totalVariation p q^2)).toReal≤
        (klDiv p.toMeasure q.toMeasure).toReal :=
      (ENNReal.toReal_le_toReal (by finiteness) hfinite).mpr hs
    rwa [ENNReal.toReal_ofReal (by positivity)] at ht
  have hn:0≤(klDiv p.toMeasure q.toMeasure).toReal/2:=by positivity
  have hsqrt:=Real.sq_sqrt hn
  nlinarith [Real.sqrt_nonneg ((klDiv p.toMeasure q.toMeasure).toReal/2)]

end SafeLearning.CompleteAppliedFinitePinsker
