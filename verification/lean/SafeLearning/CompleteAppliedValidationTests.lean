import SafeLearning.CompleteAppliedValidation
import SafeLearning.CompleteAppliedValidationNumbers
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedValidationTests
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def onePercent : unitInterval := ⟨1/100,by norm_num⟩
def twoPercent : unitInterval := ⟨1/50,by norm_num⟩

/-- The fixed-parameter null boundary really realizes the sample-size thresholds. -/
theorem actual_single_zero_failure_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 onePercent) μ) :
    μ.real {omega | ∀ i,X i omega=0}≤1/20 ↔ 299≤n := by
  rw [SafeLearning.CompleteAppliedValidation.zero_failure_probability μ n X onePercent hInd hLaw]
  norm_num only [onePercent,show (1:ℝ)-1/100=99/100 by norm_num]
  exact SafeLearning.CompleteAppliedValidationNumbers.single_real_sample_minimum n

theorem actual_twenty_budget_zero_failure_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 onePercent) μ) :
    μ.real {omega | ∀ i,X i omega=0}≤1/400 ↔ 597≤n := by
  rw [SafeLearning.CompleteAppliedValidation.zero_failure_probability μ n X onePercent hInd hLaw]
  norm_num only [onePercent,show (1:ℝ)-1/100=99/100 by norm_num]
  exact SafeLearning.CompleteAppliedValidationNumbers.twenty_real_sample_minimum n

theorem actual_299_zero_failure_strict {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 299 → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ)
    (hNull : (1/100:ℝ)≤p) : μ.real {omega | ∀ i,X i omega=0}<1/20 :=
  (SafeLearning.CompleteAppliedValidation.zero_failure_null_bound μ 299 X p hInd hLaw hNull).trans_lt
    SafeLearning.CompleteAppliedValidationNumbers.single_power_strict

/-- A zero observation is interpreted on the confidence event, over repeated samples. -/
theorem zero_observation_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 1000 → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    19/20≤μ.real {omega | (∀ i,X i omega=0) →
      (p:ℝ)≤Real.sqrt (Real.log 20/2000)} := by
  apply (SafeLearning.CompleteAppliedValidation.validation_1000_confidence μ X p hInd hm hLaw).trans
  refine measureReal_mono ?_ (by finiteness)
  intro omega hConfidence hZero
  change (p:ℝ)≤(1/1000)*∑ i,X i omega+Real.sqrt (Real.log 20/2000) at hConfidence
  have hsum : (∑ i,X i omega)=0 := Finset.sum_eq_zero (fun i _ => hZero i)
  simpa only [hsum,mul_zero,zero_add] using hConfidence

/-- A population failure probability of 2% can produce zero observed failures. -/
theorem positive_zero_failure_probability_at_two_percent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 twoPercent) μ) :
    0<μ.real {omega | ∀ i,X i omega=0} := by
  rw [SafeLearning.CompleteAppliedValidation.zero_failure_probability μ n X twoPercent hInd hLaw]
  dsimp [twoPercent]
  positivity

theorem zero_failures_do_not_imply_zero_population {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 twoPercent) μ) :
    ∃ omega,(∀ i,X i omega=0) ∧ (twoPercent:ℝ)≠0 := by
  have hp := positive_zero_failure_probability_at_two_percent μ n X hInd hLaw
  have hne : μ {omega | ∀ i,X i omega=0}≠0 := by
    intro hzero
    simp only [Measure.real,hzero,ENNReal.toReal_zero] at hp
    linarith
  obtain ⟨omega,homega⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨omega,homega,by norm_num [twoPercent]⟩

/-- With probability at least 95%, every predeclared controller accepted after zero failures
has failure probability below 1%; cross-controller dependence is unrestricted. -/
theorem twenty_simultaneous_acceptance_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 20 → Fin 597 → Ω → ℝ)
    (p : Fin 20 → unitInterval) (hInd : ∀ k,iIndepFun (X k) μ)
    (hm : ∀ k i,Measurable (X k i))
    (hLaw : ∀ k i,HasLaw (X k i) (bernoulliMeasure (1:ℝ) 0 (p k)) μ) :
    19/20≤μ.real {omega | ∀ k,(∀ i,X k i omega=0) → (p k:ℝ)<1/100} := by
  let F : Fin 20 → Set Ω := fun k =>
    {omega | (1/100:ℝ)≤p k ∧ ∀ i,X k i omega=0}
  have hZero : ∀ k,MeasurableSet {omega | ∀ i,X k i omega=0} := by
    intro k
    have h : MeasurableSet (⋂ i,{omega | X k i omega=0}) :=
      MeasurableSet.iInter (fun i => measurableSet_eq_fun (hm k i) measurable_const)
    simpa only [Set.iInter_setOf] using h
  have hF : ∀ k,MeasurableSet (F k) := by
    intro k
    by_cases hp : (1/100:ℝ)≤p k
    · simpa only [F,hp,true_and] using hZero k
    · have he : F k=∅ := by ext omega;simp only [F,Set.mem_setOf_eq,Set.mem_empty_iff_false];tauto
      rw [he]
      exact MeasurableSet.empty
  have hu := SafeLearning.CompleteAppliedValidation.twenty_zero_failure_false_accept_bound
    μ X p hInd hLaw
  have hc := probReal_compl_eq_one_sub (μ := μ) (MeasurableSet.iUnion hF)
  have he : (⋃ k,F k)ᶜ={omega | ∀ k,(∀ i,X k i omega=0) → (p k:ℝ)<1/100} := by
    ext omega
    simp only [Set.mem_compl_iff,Set.mem_iUnion,F,Set.mem_setOf_eq]
    constructor
    · intro h k hzero
      exact lt_of_not_ge (fun hp => h ⟨k,hp,hzero⟩)
    · intro h ⟨k,hp,hzero⟩
      exact (not_lt_of_ge hp) (h k hzero)
  rw [he] at hc
  change μ.real (⋃ k,F k)≤1/20 at hu
  linarith

/-- Outcome-dependent selection within the fixed family inherits the simultaneous bound. -/
theorem selected_predeclared_controller_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 20 → Fin 597 → Ω → ℝ)
    (p : Fin 20 → unitInterval) (hInd : ∀ k,iIndepFun (X k) μ)
    (hm : ∀ k i,Measurable (X k i))
    (hLaw : ∀ k i,HasLaw (X k i) (bernoulliMeasure (1:ℝ) 0 (p k)) μ)
    (selected : Ω → Fin 20) :
    19/20≤μ.real {omega | (∀ i,X (selected omega) i omega=0) →
      (p (selected omega):ℝ)<1/100} := by
  apply (twenty_simultaneous_acceptance_confidence μ X p hInd hm hLaw).trans
  refine measureReal_mono ?_ (by finiteness)
  intro omega h
  exact h (selected omega)

end SafeLearning.CompleteAppliedValidationTests
