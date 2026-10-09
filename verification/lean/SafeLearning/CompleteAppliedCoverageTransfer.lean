import SafeLearning.CompleteAppliedConfidence
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedCoverageTransfer
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Membership of the actual dynamics in a learned set is the event to which robustness applies. -/
theorem learned_model_coverage_to_safety {Ω Model : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (learned : Ω → Set Model)
    (actual : Model) (assumptions : Ω → Prop) (safe : Ω → Model → Prop)
    (hAssumptions : ∀ omega,assumptions omega)
    (hRobust : ∀ omega,assumptions omega → ∀ model ∈ learned omega,safe omega model)
    (hCoverage : (99/100:ℝ)≤μ.real {omega | actual ∈ learned omega}) :
    (99/100:ℝ)≤μ.real {omega | safe omega actual} := by
  apply hCoverage.trans
  refine measureReal_mono ?_ (by finiteness)
  intro omega hmember
  exact hRobust omega (hAssumptions omega) actual hmember

/-- Two learned sets use an event intersection; no independence between their errors is required. -/
theorem two_learned_sets_coverage_to_safety {Ω Model₁ Model₂ : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (learned₁ : Ω → Set Model₁) (learned₂ : Ω → Set Model₂)
    (actual₁ : Model₁) (actual₂ : Model₂) (assumptions safe : Ω → Prop)
    (hMeas₁ : MeasurableSet {omega | actual₁ ∈ learned₁ omega})
    (hMeas₂ : MeasurableSet {omega | actual₂ ∈ learned₂ omega})
    (hAssumptions : ∀ omega,assumptions omega)
    (hRobust : ∀ omega,assumptions omega → actual₁ ∈ learned₁ omega →
      actual₂ ∈ learned₂ omega → safe omega)
    (hCoverage₁ : (99/100:ℝ)≤μ.real {omega | actual₁ ∈ learned₁ omega})
    (hCoverage₂ : (98/100:ℝ)≤μ.real {omega | actual₂ ∈ learned₂ omega}) :
    (97/100:ℝ)≤μ.real {omega | safe omega} := by
  let E₁ : Set Ω := {omega | actual₁ ∈ learned₁ omega}
  let E₂ : Set Ω := {omega | actual₂ ∈ learned₂ omega}
  have hc₁ := probReal_compl_eq_one_sub (μ := μ) hMeas₁
  have hc₂ := probReal_compl_eq_one_sub (μ := μ) hMeas₂
  have hf₁ : μ.real E₁ᶜ≤1/100 := by dsimp [E₁];linarith
  have hf₂ : μ.real E₂ᶜ≤2/100 := by dsimp [E₂];linarith
  have hu : μ.real (E₁ᶜ ∪ E₂ᶜ)≤3/100 := by
    linarith [measureReal_union_le (μ := μ) E₁ᶜ E₂ᶜ]
  have hc := probReal_compl_eq_one_sub (μ := μ) (hMeas₁.compl.union hMeas₂.compl)
  change μ.real (E₁ᶜ ∪ E₂ᶜ)ᶜ=1-μ.real (E₁ᶜ ∪ E₂ᶜ) at hc
  rw [Set.compl_union,compl_compl,compl_compl] at hc
  have hBoth : (97/100:ℝ)≤μ.real (E₁ ∩ E₂) := by linarith
  apply hBoth.trans
  refine measureReal_mono ?_ (by finiteness)
  intro omega hmember
  exact hRobust omega (hAssumptions omega) hmember.1 hmember.2

/-- One state, uniformly chosen from 100, receives an erroneous interval. -/
def omittedStateLaw : PMF (Fin 100) := PMF.uniformOfFintype (Fin 100)
def omittedStateMeasure : Measure (Fin 100) := omittedStateLaw.toMeasure
instance omitted_state_probability : IsProbabilityMeasure omittedStateMeasure := by
  unfold omittedStateMeasure
  infer_instance

def learnedBand (omitted state : Fin 100) : Set ℝ :=
  if state=omitted then Set.Icc 1 2 else Set.Icc (-1) 1

/-- The actual dynamics value is zero at every state. -/
def trueDynamics (_state : Fin 100) : ℝ := 0

theorem band_covers_iff (omitted state : Fin 100) :
    trueDynamics state ∈ learnedBand omitted state ↔ omitted≠state := by
  by_cases h : state=omitted
  · subst state
    simp [learnedBand,trueDynamics]
  · simp [learnedBand,trueDynamics,h,Ne.symm h]

theorem pointwise_actual_99_percent (state : Fin 100) :
    omittedStateMeasure.real {omitted | trueDynamics state ∈ learnedBand omitted state}=99/100 := by
  have hset : {omitted | trueDynamics state ∈ learnedBand omitted state}=
      ({state}:Set (Fin 100))ᶜ := by
    ext omitted
    simp [band_covers_iff]
  rw [hset,probReal_compl_eq_one_sub (measurableSet_singleton state)]
  have hsingle : omittedStateMeasure.real {state}=1/100 := by
    unfold omittedStateMeasure omittedStateLaw Measure.real
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton state),
      PMF.uniformOfFintype_apply]
    norm_num
  rw [hsingle]
  norm_num

theorem simultaneous_actual_zero_percent :
    omittedStateMeasure.real {omitted | ∀ state,trueDynamics state ∈ learnedBand omitted state}=0 := by
  have hset : {omitted | ∀ state,trueDynamics state ∈ learnedBand omitted state}=
      (∅:Set (Fin 100)) := by
    ext omitted
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    intro h
    exact ((band_covers_iff omitted omitted).mp (h omitted)) rfl
  rw [hset]
  simp

/-- The same counterexample is an actual random function model set, not just an event table. -/
def learnedFunctionSet (omitted : Fin 100) : Set (Fin 100 → ℝ) :=
  {model | ∀ state,model state ∈ learnedBand omitted state}

theorem actual_function_coverage_zero :
    omittedStateMeasure.real {omitted | trueDynamics ∈ learnedFunctionSet omitted}=0 :=
  simultaneous_actual_zero_percent

end SafeLearning.CompleteAppliedCoverageTransfer
