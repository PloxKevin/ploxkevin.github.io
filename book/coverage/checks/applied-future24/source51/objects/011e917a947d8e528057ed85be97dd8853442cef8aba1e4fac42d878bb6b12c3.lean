import SafeLearning.CompleteAppliedConfidence
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConfidenceIdentities
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem hoeffding_log_threshold (N : ℝ) :
    2*Real.exp (-N/50)≤1/20 ↔ 50*Real.log 40≤N := by
  have he : Real.exp (-Real.log (40:ℝ))=1/40 := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  have hh : 2*Real.exp (-N/50)≤1/20 ↔ Real.exp (-N/50)≤1/40 := by
    constructor <;> intro h <;> linarith
  rw [hh,← he,Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem independent_three_pass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 3 → Set Ω)
    (hm : ∀ i,MeasurableSet (failure i)) (hi : iIndepSet failure μ)
    (hp : ∀ i,μ.real (failure i)=1/100) :
    μ.real (⋂ i,(failure i)ᶜ)=(99/100:ℝ)^3 := by
  have hf := SafeLearning.CompleteAppliedProbabilityModel.independent_batch_failure μ 3
    failure (1/100) hm hi hp
  have hc := probReal_compl_eq_one_sub (μ := μ) (MeasurableSet.iUnion hm)
  rw [Set.compl_iUnion,hf] at hc
  norm_num at hc ⊢
  exact hc

theorem three_failure_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 3 → Set Ω)
    (hb : ∀ i,μ.real (failure i)≤1/100) :
    μ.real (⋃ i,failure i)≤3/100 := by
  have hh := (measureReal_iUnion_fintype_le (μ := μ) failure).trans
    (Finset.sum_le_sum (fun i _ => hb i))
  norm_num at hh
  exact hh

end SafeLearning.CompleteAppliedConfidenceIdentities
