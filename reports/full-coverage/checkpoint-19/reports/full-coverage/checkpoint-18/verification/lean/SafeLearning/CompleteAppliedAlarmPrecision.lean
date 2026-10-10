import SafeLearning.CompleteAppliedAlarmBatches
import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedAlarmPrecision
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedAlarmBatches
open scoped ENNReal NNReal Classical

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem source_union_decimal_is_rounded :
    (1-(99/100:ℝ)^500)≠993/1000 ∧
      |(1-(99/100:ℝ)^500)-993/1000|<1/2000 := by
  constructor
  · norm_num [div_pow]
  · rw [abs_lt]
    constructor <;> norm_num [div_pow]

theorem actual_strict_500_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Fin 500 → Set Ω)
    (q : ℝ) (hq : q<1/10000) (hF : ∀ i,μ.real (F i)≤q) :
    μ.real (⋃ i,F i)<1/20 := by
  have hu:=measureReal_iUnion_fintype_le (μ:=μ) F
  have hs:(∑ i:Fin 500,μ.real (F i))≤500*q := by
    calc
      _≤∑ i:Fin 500,q := Finset.sum_le_sum (fun i _=>hF i)
      _=500*q := by simp
  linarith

def finiteSharpLaw (m : ℕ) [NeZero m] : PMF (Fin m) := PMF.uniformOfFintype (Fin m)
def finiteSharpAlarm {n m : ℕ} (h : n ≤ m) (i : Fin n) : Set (Fin m) := {Fin.castLE h i}

theorem finite_sharp_alarm_probability {n m : ℕ} [NeZero m] (h : n ≤ m) (i : Fin n) :
    (finiteSharpLaw m).toMeasure.real (finiteSharpAlarm h i)=1/(m:ℝ) := by
  unfold Measure.real finiteSharpAlarm finiteSharpLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply,ENNReal.toReal_inv]

theorem finite_sharp_alarm_disjoint {n m : ℕ} (h : n ≤ m) :
    Pairwise (fun i j => Disjoint (finiteSharpAlarm h i) (finiteSharpAlarm h j)) := by
  intro i j hij
  apply Set.disjoint_singleton.mpr
  intro he
  exact hij (Fin.castLE_injective h he)

theorem finite_sharp_union_probability {n m : ℕ} [NeZero m] (h : n ≤ m) :
    (finiteSharpLaw m).toMeasure.real (⋃ i,finiteSharpAlarm h i)=(n:ℝ)/(m:ℝ) := by
  rw [measureReal_iUnion_fintype (finite_sharp_alarm_disjoint h)
    (fun i=>measurableSet_singleton _),show
    (∑ i:Fin n,(finiteSharpLaw m).toMeasure.real (finiteSharpAlarm h i))=
      ∑ i:Fin n,(1/(m:ℝ)) from Finset.sum_congr rfl (fun i _=>finite_sharp_alarm_probability h i)]
  simp [div_eq_mul_inv]

def sharpLaw : PMF (Fin 10000) := finiteSharpLaw 10000
def sharpAlarm : Fin 500 → Set (Fin 10000) :=
  finiteSharpAlarm (by decide : 500≤10000)

theorem actual_union_bound_endpoint_attained :
    (∀ i,sharpLaw.toMeasure.real (sharpAlarm i)=1/10000) ∧
      sharpLaw.toMeasure.real (⋃ i,sharpAlarm i)=1/20 := by
  constructor
  · intro i
    exact finite_sharp_alarm_probability (by decide : 500≤10000) i
  · change (finiteSharpLaw 10000).toMeasure.real
      (⋃ i:Fin 500,finiteSharpAlarm (by decide : 500≤10000) i)=1/20
    rw [finite_sharp_union_probability]
    norm_num

theorem endpoint_does_not_guarantee_strict_target :
    ¬sharpLaw.toMeasure.real (⋃ i,sharpAlarm i)<1/20 := by
  rw [actual_union_bound_endpoint_attained.2]
  exact lt_irrefl _

end SafeLearning.CompleteAppliedAlarmPrecision
