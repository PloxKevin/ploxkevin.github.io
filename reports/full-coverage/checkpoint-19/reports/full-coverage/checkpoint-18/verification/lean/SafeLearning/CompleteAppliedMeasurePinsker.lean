import SafeLearning.CompleteAppliedBinaryPinsker
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedMeasurePinsker
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedTwoAtomRisk
open SafeLearning.CompleteAppliedBinaryPinsker
open scoped ENNReal NNReal Classical

def measurableTotalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ :=
  sSup {d | ∃ E : Set Ω,MeasurableSet E ∧ d=|μ.real E-ν.real E|}
def eventParameter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) : unitInterval :=
  ⟨μ.real E,measureReal_nonneg,measureReal_le_one⟩
def eventIndicator {Ω : Type*} (E : Set Ω) (omega : Ω) : Fin 2 := if omega∈E then 1 else 0

theorem actual_event_indicator_measurable {Ω : Type*} [MeasurableSpace Ω]
    (E : Set Ω) (hE : MeasurableSet E) : Measurable (eventIndicator E) :=
  Measurable.ite hE measurable_const measurable_const

theorem actual_event_indicator_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) :
    μ.map (eventIndicator E)=(costLaw (eventParameter μ E)).toMeasure := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (actual_event_indicator_measurable E hE) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  fin_cases k
  · change μ (eventIndicator E ⁻¹' {(0:Fin 2)})=(costLaw (eventParameter μ E)) 0
    have he:eventIndicator E ⁻¹' {(0:Fin 2)}=Eᶜ := by
      ext omega
      by_cases h:omega∈E <;> simp [eventIndicator,h]
    rw [he]
    change μ Eᶜ=ENNReal.ofReal (1-μ.real E)
    rw [← probReal_compl_eq_one_sub hE]
    exact (ENNReal.ofReal_toReal (by finiteness)).symm
  · change μ (eventIndicator E ⁻¹' {(1:Fin 2)})=(costLaw (eventParameter μ E)) 1
    have he:eventIndicator E ⁻¹' {(1:Fin 2)}=E := by
      ext omega
      by_cases h:omega∈E <;> simp [eventIndicator,h]
    rw [he]
    change μ E=ENNReal.ofReal (μ E).toReal
    exact (ENNReal.ofReal_toReal (by finiteness)).symm

theorem actual_measurable_event_pinsker_squared {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set Ω) (hE : MeasurableSet E) :
    ENNReal.ofReal (2*|μ.real E-ν.real E|^2)≤klDiv μ ν := by
  have hp:=actual_binary_pinsker (eventParameter μ E) (eventParameter ν E)
  rw [actual_binary_total_variation] at hp
  apply hp.trans
  rw [← actual_event_indicator_law μ E hE,← actual_event_indicator_law ν E hE]
  exact klDiv_map_le _ _ (actual_event_indicator_measurable E hE)

theorem actual_measure_tv_range {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ measurableTotalVariation μ ν ∧ measurableTotalVariation μ ν≤1 := by
  have hu:∀ d∈{d | ∃ E : Set Ω,MeasurableSet E ∧ d=|μ.real E-ν.real E|},d≤1 := by
    rintro d ⟨E,_,rfl⟩
    rw [abs_le]
    constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=E),
      measureReal_nonneg (μ:=ν) (s:=E),measureReal_le_one (μ:=μ) (s:=E),
      measureReal_le_one (μ:=ν) (s:=E)]
  have hb:BddAbove {d | ∃ E : Set Ω,MeasurableSet E ∧ d=|μ.real E-ν.real E|}:=⟨1,hu⟩
  have hzero:(0:ℝ)∈{d | ∃ E : Set Ω,MeasurableSet E ∧ d=|μ.real E-ν.real E|} :=
    ⟨∅,MeasurableSet.empty,by simp⟩
  exact ⟨le_csSup hb hzero,csSup_le ⟨0,hzero⟩ hu⟩

theorem actual_measure_pinsker_finite_real {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : klDiv μ ν≠⊤) :
    measurableTotalVariation μ ν≤Real.sqrt ((klDiv μ ν).toReal/2) := by
  apply csSup_le
  · exact ⟨0,∅,MeasurableSet.empty,by simp⟩
  · rintro d ⟨E,hE,rfl⟩
    have hs:=actual_measurable_event_pinsker_squared μ ν E hE
    have hr:2*|μ.real E-ν.real E|^2≤(klDiv μ ν).toReal := by
      have ht: (ENNReal.ofReal (2*|μ.real E-ν.real E|^2)).toReal≤(klDiv μ ν).toReal :=
        (ENNReal.toReal_le_toReal (by finiteness) hfinite).mpr hs
      rwa [ENNReal.toReal_ofReal (by positivity)] at ht
    have hn:0≤(klDiv μ ν).toReal/2:=by positivity
    have hsq:=Real.sq_sqrt hn
    nlinarith [Real.sqrt_nonneg ((klDiv μ ν).toReal/2)]

/-- Pinsker for arbitrary probability measures; divergence at infinity is retained. -/
theorem actual_measure_pinsker_squared {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2*measurableTotalVariation μ ν^2)≤klDiv μ ν := by
  by_cases htop:klDiv μ ν=⊤
  · rw [htop]
    exact le_top
  · have hu:=actual_measure_pinsker_finite_real μ ν htop
    have ht:= (actual_measure_tv_range μ ν).1
    have hs:=Real.sq_sqrt (show 0≤(klDiv μ ν).toReal/2 by positivity)
    have hr:2*measurableTotalVariation μ ν^2≤(klDiv μ ν).toReal := by
      nlinarith [Real.sqrt_nonneg ((klDiv μ ν).toReal/2)]
    calc
      _≤ENNReal.ofReal (klDiv μ ν).toReal:=ENNReal.ofReal_le_ofReal hr
      _=_:=ENNReal.ofReal_toReal htop

end SafeLearning.CompleteAppliedMeasurePinsker
