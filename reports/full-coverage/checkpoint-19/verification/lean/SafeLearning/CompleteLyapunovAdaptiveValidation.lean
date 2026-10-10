import SafeLearning.CompleteLyapunovValidationConfidence

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteLyapunovAdaptiveValidation
open SafeLearning.CompleteLyapunovValidationConfidence

/-- History may contain earlier results and retraining; the current holdout is independent. -/
theorem genuine_product_bad_event_bound {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (ν : Measure H) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (bad : Set (H × Ω)) (hb : MeasurableSet bad) (delta : ℝ)
    (hsections : ∀ h, μ.real (Prod.mk h ⁻¹' bad) ≤ delta) :
    (ν.prod μ).real bad ≤ delta := by
  have hsec : ∀ h, μ (Prod.mk h ⁻¹' bad) ≤ ENNReal.ofReal delta := by
    intro h
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hsections h)
  have hprod : (ν.prod μ) bad ≤ ENNReal.ofReal delta := by
    rw [Measure.prod_apply hb]
    calc
      _ ≤ ∫⁻ _h, ENNReal.ofReal delta ∂ν := lintegral_mono hsec
      _ = ENNReal.ofReal delta := by simp
  have hd : 0 ≤ delta := measureReal_nonneg.trans (hsections (by
    have : Nonempty H := nonempty_of_isProbabilityMeasure ν
    exact Classical.choice this))
  exact (ENNReal.toReal_mono (by finiteness) hprod).trans_eq (ENNReal.toReal_ofReal hd)

def badEvent {H Ω : Type*} (n : ℕ) (X : Fin n → H × Ω → ℝ)
    (p : H → unitInterval) (delta critical : ℝ) : Set (H × Ω) :=
  {w | average n (fun i v => X i (w.1,v)) w.2 + radius 2 delta n ≤ 1-critical ∧
    1-(p w.1 : ℝ) < critical}

theorem genuine_bad_event_measurable {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (n : ℕ) (X : Fin n → H × Ω → ℝ) (p : H → unitInterval)
    (delta critical : ℝ) (hm : ∀ i, Measurable (X i))
    (hp : Measurable (fun h => (p h : ℝ))) :
    MeasurableSet (badEvent n X p delta critical) := by
  have hmean : Measurable (fun w : H × Ω => average n (fun i v => X i (w.1,v)) w.2) :=
    measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ => hm i))
  exact (measurableSet_le (hmean.add_const _) measurable_const).inter
    (measurableSet_lt (measurable_const.sub (hp.comp measurable_fst)) measurable_const)

theorem genuine_history_dependent_bad_event_bound {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (ν : Measure H) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) (X : Fin n → H × Ω → ℝ) (p : H → unitInterval)
    (delta critical : ℝ) (hd : 0<delta) (hd1 : delta≤1)
    (hm : ∀ i, Measurable (X i)) (hp : Measurable (fun h => (p h : ℝ)))
    (hInd : ∀ h, iIndepFun (fun i v => X i (h,v)) μ)
    (hLaw : ∀ h i, HasLaw (fun v => X i (h,v)) (bernoulliMeasure (1:ℝ) 0 (p h)) μ) :
    (ν.prod μ).real (badEvent n X p delta critical) ≤ delta := by
  have hb := genuine_bad_event_measurable n X p delta critical hm hp
  apply genuine_product_bad_event_bound ν μ _ hb delta
  intro h
  have hs : MeasurableSet (Prod.mk h ⁻¹' badEvent n X p delta critical) :=
    measurable_prodMk_left hb
  have hc := probReal_compl_eq_one_sub (μ := μ) hs
  have ht := genuine_two_sided_acceptance_guarantee μ n hn
    (fun i v => X i (h,v)) (p h) delta critical hd hd1 (hInd h)
    (fun i => (hm i).comp measurable_prodMk_left) (hLaw h)
  have he : (Prod.mk h ⁻¹' badEvent n X p delta critical)ᶜ =
      {v | (average n (fun i v => X i (h,v)) v + radius 2 delta n ≤ 1-critical) →
        critical ≤ 1-(p h : ℝ)} := by
    ext v
    simp [badEvent, imp_iff_not_or]
  rw [he] at hc
  linarith

/-- Five adaptive attempts, each with independent fresh data conditional on its history.
The attempts themselves need not be independent, and stopping can depend on earlier results. -/
theorem genuine_five_adaptive_attempts_overall_confidence {Z H Ω : Type*}
    [MeasurableSpace Z] [MeasurableSpace H] [MeasurableSpace Ω]
    (ρ : Measure Z) (ν : Fin 5 → Measure H) (μ : Measure Ω)
    [IsProbabilityMeasure ρ] [∀ k, IsProbabilityMeasure (ν k)] [IsProbabilityMeasure μ]
    (Y : Fin 5 → Z → H × Ω) (hY : ∀ k, Measurable (Y k))
    (hFresh : ∀ k, HasLaw (Y k) ((ν k).prod μ) ρ)
    (n : ℕ) (hn : 0<n) (X : Fin 5 → Fin n → H × Ω → ℝ)
    (p : Fin 5 → H → unitInterval) (critical : ℝ)
    (hm : ∀ k i, Measurable (X k i))
    (hp : ∀ k, Measurable (fun h => (p k h : ℝ)))
    (hInd : ∀ k h, iIndepFun (fun i v => X k i (h,v)) μ)
    (hLaw : ∀ k h i, HasLaw (fun v => X k i (h,v))
      (bernoulliMeasure (1:ℝ) 0 (p k h)) μ) :
    99/100 ≤ ρ.real {z | ∀ k : Fin 5,
      average n (fun i v => X k i ((Y k z).1,v)) (Y k z).2 + radius 2 (1/500) n
        ≤ 1-critical → critical ≤ 1-(p k (Y k z).1 : ℝ)} := by
  let bad : Fin 5 → Set Z := fun k => Y k ⁻¹' badEvent n (X k) (p k) (1/500) critical
  have hb : ∀ k, MeasurableSet (bad k) := fun k =>
    hY k (genuine_bad_event_measurable n (X k) (p k) (1/500) critical (hm k) (hp k))
  have hbound : ∀ k, ρ.real (bad k) ≤ 1/500 := by
    intro k
    have he := (hFresh k).measureReal_eq
      (genuine_bad_event_measurable n (X k) (p k) (1/500) critical (hm k) (hp k))
    change ρ.real (bad k) = ((ν k).prod μ).real (badEvent n (X k) (p k) (1/500) critical) at he
    rw [he]
    exact genuine_history_dependent_bad_event_bound (ν k) μ n hn (X k) (p k)
      (1/500) critical (by norm_num) (by norm_num) (hm k) (hp k) (hInd k) (hLaw k)
  have hu := (measureReal_iUnion_fintype_le (μ := ρ) bad).trans
    (Finset.sum_le_sum (fun k _ => hbound k))
  have hu1 : ρ.real (⋃ k, bad k) ≤ 1/100 := by norm_num at hu ⊢; exact hu
  have hc := probReal_compl_eq_one_sub (μ := ρ) (MeasurableSet.iUnion hb)
  have he : (⋃ k, bad k)ᶜ = {z | ∀ k : Fin 5,
      average n (fun i v => X k i ((Y k z).1,v)) (Y k z).2 + radius 2 (1/500) n
        ≤ 1-critical → critical ≤ 1-(p k (Y k z).1 : ℝ)} := by
    ext z
    simp [bad,badEvent, imp_iff_not_or]
  rw [he] at hc
  linarith

end SafeLearning.CompleteLyapunovAdaptiveValidation
