import SafeLearning.CompleteLyapunovValidationConfidence

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteLyapunovTrajectoryValidation
open SafeLearning.CompleteLyapunovValidationConfidence

def trajectory {S A : Type*} (f : S × A → S) (pi : S → A) : ℕ → S → S
  | 0 => id
  | n+1 => fun s => f (trajectory f pi n s, pi (trajectory f pi n s))

theorem genuine_trajectory_measurable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (f : S × A → S) (pi : S → A) (hf : Measurable f) (hp : Measurable pi) :
    ∀ n, Measurable (trajectory f pi n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact hf.comp (ih.prodMk (hp.comp ih))

/-- The actual approximate-controller trajectory reaches the terminal set and respects
the error bound at every state before its first entry. -/
def goodInitialStates {S A : Type*} [NormedAddCommGroup A]
    (f : S × A → S) (approx mpc : S → A) (terminal : Set S) (eta : ℝ) : Set S :=
  {s | ∃ T : ℕ, trajectory f approx T s ∈ terminal ∧
    ∀ t : ℕ, t<T → trajectory f approx t s ∉ terminal ∧
      ‖approx (trajectory f approx t s)-mpc (trajectory f approx t s)‖ ≤ eta}

theorem genuine_good_initial_states_measurable {S A : Type*}
    [MeasurableSpace S] [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A]
    (f : S × A → S) (approx mpc : S → A) (terminal : Set S) (eta : ℝ)
    (hf : Measurable f) (ha : Measurable approx) (hm : Measurable mpc)
    (ht : MeasurableSet terminal) : MeasurableSet (goodInitialStates f approx mpc terminal eta) := by
  have htr := genuine_trajectory_measurable f approx hf ha
  have he : ∀ t, Measurable (fun s =>
      ‖approx (trajectory f approx t s)-mpc (trajectory f approx t s)‖) :=
    fun t => ((ha.comp (htr t)).sub (hm.comp (htr t))).norm
  have heq : goodInitialStates f approx mpc terminal eta =
      ⋃ T : ℕ, {s | trajectory f approx T s ∈ terminal} ∩
        ⋂ t : ℕ, {s | t<T → trajectory f approx t s ∉ terminal ∧
          ‖approx (trajectory f approx t s)-mpc (trajectory f approx t s)‖ ≤ eta} := by
    ext s
    simp [goodInitialStates]
  rw [heq]
  apply MeasurableSet.iUnion
  intro T
  apply (htr T ht).inter
  apply MeasurableSet.iInter
  intro t
  by_cases h : t<T
  · convert ((htr t ht).compl.inter (measurableSet_le (he t)
      (show Measurable (fun _ : S => eta) from measurable_const))) using 1
    ext s
    simp [h]
  · simp [h]

/-- A measurable actual trajectory-failure event has its actual Bernoulli law,
without assuming that law or a desired success probability. -/
theorem genuine_initial_state_failure_indicator_law {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (good : Set S) (hg : MeasurableSet good) :
    HasLaw (goodᶜ.indicator (fun _ : S => (1 : ℝ)))
      (bernoulliMeasure (1:ℝ) 0 ⟨μ.real goodᶜ, by simp⟩) μ :=
  hasLaw_indicator_bernoulliMeasure 1 hg.compl.nullMeasurableSet

theorem genuine_initial_state_iid_trials_acceptance {Z S : Type*}
    [MeasurableSpace Z] [MeasurableSpace S]
    (ρ : Measure Z) (μ : Measure S) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (good : Set S) (hg : MeasurableSet good) (n : ℕ) (hn : 0<n)
    (initial : Fin n → Z → S) (hi : ∀ i, Measurable (initial i))
    (hInd : iIndepFun initial ρ) (hLaw : ∀ i, HasLaw (initial i) μ ρ)
    (delta critical : ℝ) (hd : 0<delta) (hd1 : delta≤1) :
    1-delta ≤ ρ.real {z | average n
      (fun i => goodᶜ.indicator (fun _ : S => (1:ℝ)) ∘ initial i) z + radius 2 delta n
      ≤ 1-critical → critical ≤ μ.real good} := by
  let fail : S → ℝ := goodᶜ.indicator (fun _ => (1:ℝ))
  have hm : Measurable fail := measurable_const.indicator hg.compl
  have hp := genuine_initial_state_failure_indicator_law μ good hg
  have h := genuine_two_sided_acceptance_guarantee ρ n hn
    (fun i => fail ∘ initial i) ⟨μ.real goodᶜ, by simp⟩ delta critical hd hd1
    (hInd.comp (fun _ => fail) (fun _ => hm))
    (fun i => hm.comp (hi i)) (fun i => hp.comp (hLaw i))
  have hc := probReal_compl_eq_one_sub (μ := μ) hg
  simpa only [hc, sub_sub_cancel, fail] using h

end SafeLearning.CompleteLyapunovTrajectoryValidation
