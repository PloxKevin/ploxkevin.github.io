import SafeLearning.CompleteAppliedProbabilityModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteClaims
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedProbabilityModel
open scoped NNReal ENNReal

theorem finite_indicator_expectation {n : ℕ} (law : PMF (Fin n)) (E : Set (Fin n)) :
    finiteExpectation law (E.indicator (fun _ => (1:ℝ)))=eventProbability law E := by
  classical
  unfold finiteExpectation eventProbability
  rw [PMF.toOuterMeasure_apply_fintype,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i ∈ E <;> simp [Set.indicator,h]
  · intro i hi
    by_cases h : i ∈ E
    · simpa [Set.indicator,h] using law.apply_ne_top i
    · simp [Set.indicator,h]

theorem finiteExpectation_const_mul {n : ℕ} (law : PMF (Fin n)) (X : Fin n → ℝ) (c : ℝ) :
    finiteExpectation law (fun i => c*X i)=c*finiteExpectation law X := by
  unfold finiteExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi; ring

theorem finite_constant_on_event {n : ℕ} (law : PMF (Fin n)) (E : Set (Fin n)) (c : ℝ) :
    finiteExpectation law (E.indicator (fun _ => c))=c*eventProbability law E := by
  classical
  have he : E.indicator (fun _ : Fin n => c)=(fun i => c*E.indicator (fun _ => (1:ℝ)) i) := by
    ext i; by_cases h : i ∈ E <;> simp [h]
  rw [he,finiteExpectation_const_mul,finite_indicator_expectation]

theorem conditional_constant_loss {n : ℕ} (law : PMF (Fin n)) (I : Set (Fin n))
    (c : ℝ) (hI : eventProbability law I ≠ 0) :
    conditionalFiniteExpectation law (fun _ => c) I=c := by
  unfold conditionalFiniteExpectation
  rw [finite_constant_on_event]
  exact mul_div_cancel_right₀ c hI

theorem conditional_fault_loss {n : ℕ} (law : PMF (Fin n)) (F I : Set (Fin n)) (loss : ℝ) :
    conditionalFiniteExpectation law (F.indicator (fun _ => loss)) I=
      loss*conditionalProbability law F I := by
  classical
  have he : I.indicator (F.indicator (fun _ : Fin n => loss))=
      (F ∩ I).indicator (fun _ => loss) := by
    ext i; by_cases hF : i ∈ F <;> by_cases hI : i ∈ I <;> simp [hF,hI]
  unfold conditionalFiniteExpectation conditionalProbability
  rw [he,finite_constant_on_event]
  ring

theorem finite_covariance_quadratic {n : ℕ} (law : PMF (Fin n))
    (X Y : Fin n → ℝ) (u v : ℝ) :
    0 ≤ u^2*finiteVariance law X+2*u*v*finiteCovariance law X Y+v^2*finiteVariance law Y := by
  have he : finiteExpectation law (fun i =>
      (u*(X i-finiteExpectation law X)+v*(Y i-finiteExpectation law Y))^2)=
      u^2*finiteVariance law X+2*u*v*finiteCovariance law X Y+v^2*finiteVariance law Y := by
    unfold finiteVariance finiteCovariance finiteExpectation
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; ring
  rw [← he]
  unfold finiteExpectation
  exact Finset.sum_nonneg (fun i hi => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

def quarterLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(1/4:ℝ≥0),3/4] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def weightedQuantity : Fin 2 → ℝ := ![2,6]
def actionReward : Fin 2 → ℝ := ![4,0]

theorem quarter_weighted_average : finiteExpectation quarterLaw weightedQuantity=5 ∧
    ((2+6+6+6:ℝ)/4)=5 ∧ (2+6:ℝ)≠5 := by
  norm_num [finiteExpectation,quarterLaw,weightedQuantity,Fin.sum_univ_succ]

theorem quarter_action_reward : finiteExpectation quarterLaw actionReward=1 ∧
    (∀ i : Fin 2, actionReward i≠1) := by
  constructor
  · norm_num [finiteExpectation,quarterLaw,actionReward,Fin.sum_univ_succ]
  · intro i; fin_cases i <;> norm_num [actionReward]

def tenPercentFaultLaw : PMF (Fin 4) := PMF.ofFintype
  (fun i => ((![(2/25:ℝ≥0),1/50,9/50,18/25] : Fin 4 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])

theorem ten_percent_fault_conditioning :
    eventProbability tenPercentFaultLaw faulty=1/10 ∧
    eventProbability tenPercentFaultLaw alarm=13/50 ∧
    eventProbability tenPercentFaultLaw (faulty ∩ alarm)=2/25 ∧
    conditionalProbability tenPercentFaultLaw faulty alarm=4/13 ∧
    conditionalProbability tenPercentFaultLaw alarm faulty=4/5 ∧
    |(4/13:ℝ)-(3077/10000)| ≤ 1/20000 := by
  norm_num [conditionalProbability,eventProbability,tenPercentFaultLaw,faulty,alarm,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,Set.indicator]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem cost_standard_deviation_rounding :
    |Real.sqrt 11/2-(1658/1000:ℝ)| ≤ 1/2000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 11)
  have hp := Real.sqrt_nonneg (11:ℝ)
  rw [abs_le]; constructor <;> nlinarith

end SafeLearning.CompleteAppliedFiniteClaims
