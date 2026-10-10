import SafeLearning.CompleteConformal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SafeLearning.CompleteConformalCounterexample

/-- A uniformly chosen coordinate is the only nonzero residual. This gives
an exchangeable joint law with nineteen calibration residuals and one test. -/
def oneHigh (ω i : Fin 20) : ℝ := if i = ω then 1 else 0

def residualLaw : PMF (Fin 20) := PMF.uniformOfFintype (Fin 20)

def residualMeasure : Measure (Fin 20) := residualLaw.toMeasure

theorem absolute_residual_realization (ω i : Fin 20) :
    |oneHigh ω i - 0| = oneHigh ω i := by
  by_cases h : i = ω <;> simp [oneHigh, h]

instance : IsProbabilityMeasure residualMeasure := by
  unfold residualMeasure
  infer_instance

theorem uniform_permutation (p : Equiv.Perm (Fin 20)) :
    residualLaw.map p = residualLaw := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (p.symm b)]
  · simp [residualLaw]
  · intro a ha
    have hb : b ≠ p a := by
      intro h
      exact ha (by simpa using congrArg p.symm h.symm)
    simp [hb]

theorem permutation_identDistrib (p : Equiv.Perm (Fin 20)) :
    IdentDistrib p id residualMeasure residualMeasure := by
  refine ⟨(measurable_of_finite p).aemeasurable, measurable_id.aemeasurable, ?_⟩
  unfold residualMeasure
  rw [PMF.toMeasure_map (f := p) residualLaw (measurable_of_finite p),
      uniform_permutation, Measure.map_id]

theorem scores_exchangeable (p : Equiv.Perm (Fin 20)) :
    IdentDistrib (fun ω i => oneHigh ω (p i)) oneHigh residualMeasure residualMeasure := by
  have h := (permutation_identDistrib p.symm).comp (measurable_of_finite oneHigh)
  convert h using 1
  · ext ω i
    simp only [oneHigh, Function.comp_apply]
    simp only [← p.eq_symm_apply]
  · rfl

def clippedThreshold (ω test : Fin 20) : EReal :=
  (Finset.univ.erase test).sup (fun i => (oneHigh ω i : EReal))

theorem calibration_nonempty (test : Fin 20) :
    (Finset.univ.erase test).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem (Finset.mem_univ test), Finset.card_univ]
  norm_num

theorem clipped_failure_iff (ω test : Fin 20) :
    clippedThreshold ω test < (oneHigh ω test : EReal) ↔ ω = test := by
  classical
  by_cases h : ω = test
  · subst ω
    have hz : clippedThreshold test test = 0 := by
      unfold clippedThreshold
      calc
        (Finset.univ.erase test).sup (fun i => (oneHigh test i : EReal)) =
            (Finset.univ.erase test).sup (fun _ => (0 : EReal)) := by
          apply Finset.sup_congr rfl
          intro i hi
          simp [oneHigh, (Finset.mem_erase.mp hi).1]
        _ = 0 := Finset.sup_const (calibration_nonempty test) 0
    simp [hz, oneHigh]
  · have hi : ω ∈ Finset.univ.erase test := Finset.mem_erase.mpr ⟨h, Finset.mem_univ ω⟩
    have hlo : (1 : EReal) ≤ clippedThreshold ω test := by
      simpa [oneHigh, clippedThreshold] using
        Finset.le_sup (f := fun i => (oneHigh ω i : EReal)) hi
    have ht : oneHigh ω test = 0 := by simp [oneHigh, Ne.symm h]
    rw [ht]
    simp only [EReal.coe_zero]
    constructor
    · intro hf
      have : (1 : EReal) < 0 := hlo.trans_lt hf
      have hbad : (1 : ℝ) < 0 := EReal.coe_lt_coe_iff.mp this
      norm_num at hbad
    · exact fun he => (h he).elim

theorem actual_clipped_failure_probability (test : Fin 20) :
    residualMeasure.real {ω | clippedThreshold ω test < (oneHigh ω test : EReal)} =
      (1 / 20 : ℝ) := by
  have he : {ω | clippedThreshold ω test < (oneHigh ω test : EReal)} = {test} := by
    ext ω
    exact clipped_failure_iff ω test
  rw [he]
  simp [residualMeasure, residualLaw, Measure.real]

theorem clipped_maximum_fails_ninety_nine_percent (test : Fin 20) :
    residualMeasure.real {ω | (oneHigh ω test : EReal) ≤ clippedThreshold ω test} =
      (19 / 20 : ℝ) ∧
    residualMeasure.real {ω | (oneHigh ω test : EReal) ≤ clippedThreshold ω test} <
      (99 / 100 : ℝ) := by
  have he : {ω | (oneHigh ω test : EReal) ≤ clippedThreshold ω test} =
      ({ω | clippedThreshold ω test < (oneHigh ω test : EReal)})ᶜ := by
    ext ω
    simp
  rw [he, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet,
      actual_clipped_failure_probability]
  norm_num

end SafeLearning.CompleteConformalCounterexample
