import SafeLearning.CompleteAppliedAlarmModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedAlarmBatches
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedProbabilityModel
open scoped ENNReal NNReal

theorem actual_false_alarm_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (F : Fin n → Set Ω)
    (hF : ∀ i,MeasurableSet (F i)) (q : ℝ) (hq : ∀ i,μ.real (F i)=q) :
    (∫ omega,∑ i:Fin n,(F i).indicator (fun _ => (1:ℝ)) omega ∂μ)=(n:ℝ)*q := by
  have hm (i : Fin n) : (∫ omega,(F i).indicator (fun _ => (1:ℝ)) omega ∂μ)=q := by
    rw [(SafeLearning.CompleteAppliedBinomialModel.actual_indicator_mean_and_variance μ (F i) (hF i)).1,hq i]
  rw [integral_finsetSum _ (fun i _ => ((memLp_const (1:ℝ)).indicator (hF i)).integrable
    (by norm_num : (1:ℝ≥0∞)≤2))]
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem actual_500_false_alarm_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Fin 500 → Set Ω)
    (hF : ∀ i,MeasurableSet (F i)) (hq : ∀ i,μ.real (F i)=(1/100:ℝ)) :
    (∫ omega,∑ i:Fin 500,(F i).indicator (fun _ => (1:ℝ)) omega ∂μ)=5 := by
  rw [actual_false_alarm_expectation μ 500 F hF (1/100) hq]
  norm_num

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem actual_500_independent_alarm_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Fin 500 → Set Ω)
    (hF : ∀ i,MeasurableSet (F i)) (hi : iIndepSet F μ)
    (hq : ∀ i,μ.real (F i)=(1/100:ℝ)) :
    μ.real (⋃ i,F i)=1-(99/100:ℝ)^500 ∧
      |μ.real (⋃ i,F i)-(993/1000:ℝ)|≤1/2000 := by
  have hp := independent_batch_failure μ 500 F (1/100) hF hi hq
  rw [show (1:ℝ)-1/100=99/100 by norm_num] at hp
  refine ⟨hp,?_⟩
  rw [hp,abs_le]
  constructor <;> norm_num [div_pow]

theorem actual_500_arbitrary_dependence_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Fin 500 → Set Ω)
    (hq : ∀ i,μ.real (F i)≤(1/10000:ℝ)) : μ.real (⋃ i,F i)≤1/20 := by
  apply (measureReal_iUnion_fintype_le F).trans
  have hs : (∑ i:Fin 500,μ.real (F i))≤∑ i:Fin 500,(1/10000:ℝ) :=
    Finset.sum_le_sum (fun i _ => hq i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num only [Nat.cast_ofNat,mul_one_div] at hs
  linarith

theorem source_per_step_false_alarm_level : (1/20:ℝ)/500=1/10000 := by norm_num

end SafeLearning.CompleteAppliedAlarmBatches
