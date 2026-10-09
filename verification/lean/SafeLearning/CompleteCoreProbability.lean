import Mathlib
import SafeLearning.CompleteBookProjects

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SafeLearning.CompleteCoreProbability

def testDistribution : Measure ℝ := (1/2 : ℝ≥0∞) • volume.restrict (Icc (-1 : ℝ) 1)
def exceptional : Set ℝ := Icc (99/100) 1
def approximationError : ℝ → ℝ := exceptional.indicator (fun _ => 1/10)

theorem uniform_test_mass : testDistribution univ=1 := by
  norm_num [testDistribution,Measure.smul_apply,Measure.restrict_apply,Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance testDistribution_isProbability : IsProbabilityMeasure testDistribution := ⟨uniform_test_mass⟩

theorem exceptional_probability : testDistribution exceptional=(1/200 : ℝ≥0∞) := by
  have hs : exceptional ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx;constructor <;> linarith [hx.1,hx.2]
  change (1/2 : ℝ≥0∞)*(volume.restrict (Icc (-1 : ℝ) 1)) exceptional=1/200
  rw [Measure.restrict_apply (show MeasurableSet exceptional from measurableSet_Icc),
    inter_eq_self_of_subset_left hs]
  norm_num [exceptional,Real.volume_Icc]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
  rw [← ENNReal.mul_inv]
  all_goals norm_num

theorem squared_error_indicator : (fun x => (approximationError x)^2)=
    exceptional.indicator (fun _ => (1/100 : ℝ)) := by
  funext x
  by_cases h : x ∈ exceptional <;> simp [approximationError,Set.indicator,h] <;> norm_num

theorem actual_mean_squared_error :
    (∫ x, (approximationError x)^2 ∂testDistribution)=(1/20000 : ℝ) := by
  rw [squared_error_indicator,integral_indicator_const (1/100 : ℝ)
    (show MeasurableSet exceptional from measurableSet_Icc)]
  simp only [Measure.real,exceptional_probability,smul_eq_mul]
  norm_num

theorem maximum_error_attained :
    (∀ x : ℝ, |approximationError x| ≤ 1/10) ∧ |approximationError 1|=1/10 := by
  constructor
  · intro x
    by_cases h : x ∈ exceptional <;> simp [approximationError,Set.indicator,h] <;> norm_num
  · norm_num [approximationError,exceptional,Set.indicator]

theorem small_rms_does_not_bound_uniform_error :
    Real.sqrt (1/20000 : ℝ) < 3/100 ∧ ¬ (∀ x : ℝ, |approximationError x| ≤ 3/100) := by
  constructor
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/20000)
    have hp := Real.sqrt_nonneg (1/20000 : ℝ)
    nlinarith
  · intro h
    have hh := h 1
    rw [maximum_error_attained.2] at hh
    norm_num at hh

theorem rms_numeric_enclosure :
    (70705/10000000 : ℝ) < Real.sqrt (1/20000 : ℝ) ∧
    Real.sqrt (1/20000 : ℝ) < 70715/10000000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/20000)
  have hp := Real.sqrt_nonneg (1/20000 : ℝ)
  constructor <;> nlinarith

theorem independent_missed_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (miss : Fin 200 → Set Ω) (hind : iIndepSet miss μ)
    (hp : ∀ i, μ (miss i)=(199/200 : ℝ≥0∞)) :
    μ (⋂ i, miss i)=(199/200 : ℝ≥0∞)^200 := by
  have h := hind.meas_biInter Finset.univ
  simpa only [Finset.mem_univ,iInter_true,Finset.prod_congr rfl (fun i _ => hp i),
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem miss_probability_numeric :
    (36695/100000 : ℚ) < (199/200 : ℚ)^200 ∧
    (199/200 : ℚ)^200 < 36705/100000 := by norm_num

theorem miss_probability_real_bridge :
    ((199/200 : ℝ≥0∞)^200).toReal=(199/200 : ℝ)^200 ∧
    (36695/100000 : ℝ) < (199/200 : ℝ)^200 ∧
    (199/200 : ℝ)^200 < 36705/100000 := by
  constructor
  · norm_num only [ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat]
  · norm_num

theorem four_success_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 4 → Set Ω)
    (hm : ∀ i, MeasurableSet (failure i))
    (hp : ∀ i, μ (failure i) ≤ (1/10 : ℝ≥0∞)) :
    (3/5 : ℝ) ≤ μ.real (⋂ i, (failure i)ᶜ) := by
  have hu := SafeLearning.CompleteBookProjects.four_failure_union μ failure hp
  have hr : μ.real (⋃ i, failure i) ≤ 2/5 := by
    have hh := ENNReal.toReal_mono (by finiteness : (2/5 : ℝ≥0∞) ≠ ⊤) hu
    norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat] at hh
    exact hh
  rw [← compl_iUnion,probReal_compl_eq_one_sub (MeasurableSet.iUnion hm)]
  linarith

theorem four_success_allocated_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 4 → Set Ω)
    (hm : ∀ i, MeasurableSet (failure i))
    (hp : ∀ i, μ (failure i) ≤ (1/40 : ℝ≥0∞)) :
    (9/10 : ℝ) ≤ μ.real (⋂ i, (failure i)ᶜ) := by
  have hu := SafeLearning.CompleteBookProjects.four_failure_allocated μ failure hp
  have hr : μ.real (⋃ i, failure i) ≤ 1/10 := by
    have hh := ENNReal.toReal_mono (by finiteness : (1/10 : ℝ≥0∞) ≠ ⊤) hu
    norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] at hh
    exact hh
  rw [← compl_iUnion,probReal_compl_eq_one_sub (MeasurableSet.iUnion hm)]
  linarith

theorem four_independent_successes {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (success : Fin 4 → Set Ω)
    (hind : iIndepSet success μ) (hp : ∀ i, μ (success i)=(9/10 : ℝ≥0∞)) :
    μ (⋂ i, success i)=(9/10 : ℝ≥0∞)^4 := by
  have h := hind.meas_biInter Finset.univ
  simpa only [Finset.mem_univ,iInter_true,Finset.prod_congr rfl (fun i _ => hp i),
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem four_independent_success_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (success : Fin 4 → Set Ω)
    (hind : iIndepSet success μ) (hp : ∀ i, (9/10 : ℝ≥0∞) ≤ μ (success i)) :
    (6561/10000 : ℝ) ≤ μ.real (⋂ i, success i) := by
  have he : μ (⋂ i, success i)=∏ i, μ (success i) := by
    simpa only [Finset.mem_univ,iInter_true] using hind.meas_biInter Finset.univ
  have hh : (9/10 : ℝ≥0∞)^4 ≤ μ (⋂ i, success i) := by
    rw [he]
    calc (9/10 : ℝ≥0∞)^4 = ∏ _i : Fin 4, (9/10 : ℝ≥0∞) := by simp
         _ ≤ ∏ i, μ (success i) := Finset.prod_le_prod (fun i _ => hp i)
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hh
  norm_num only [ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat] at hr
  norm_num at hr
  exact hr

/-- Four disjoint failures each of probability .1 give joint success .6.
This actual normalized law refutes multiplying marginals without independence. -/
def disjointFailuresLaw : PMF (Fin 5) := PMF.ofFintype
  (fun i => (((![1/10,1/10,1/10,1/10,3/5] : Fin 5 → ℝ≥0) i) : ℝ≥0∞))
  (by norm_cast;norm_num [Fin.sum_univ_succ])
def disjointFailure (i : Fin 4) : Set (Fin 5) := {i.castSucc}

theorem disjoint_failure_probabilities (i : Fin 4) :
    (disjointFailuresLaw.toOuterMeasure (disjointFailure i)).toReal=(1/10 : ℝ) := by
  fin_cases i <;> norm_num [disjointFailure,disjointFailuresLaw,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]

theorem disjoint_joint_success :
    (disjointFailuresLaw.toOuterMeasure (⋂ i, (disjointFailure i)ᶜ)).toReal=(3/5 : ℝ) := by
  have he : (⋂ i, (disjointFailure i)ᶜ)=({4} : Set (Fin 5)) := by
    ext j
    fin_cases j <;> simp [disjointFailure,Fin.forall_fin_succ]
  rw [he]
  norm_num [disjointFailuresLaw,PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,
    Fin.sum_univ_succ,Set.indicator]

theorem multiplying_marginals_invalid :
    (disjointFailuresLaw.toOuterMeasure (⋂ i, (disjointFailure i)ᶜ)).toReal < (9/10 : ℝ)^4 := by
  rw [disjoint_joint_success]
  norm_num

end SafeLearning.CompleteCoreProbability
