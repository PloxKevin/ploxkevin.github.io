import SafeLearning.CompleteCoreEntryModel
import SafeLearning.CompleteMonitoringDeficit22
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SafeLearning.CompleteSauteRepresentation22
local instance : MeasurableSpace (Fin 2 × Fin 2) := ⊤
local instance : MeasurableSingletonClass (Fin 2 × Fin 2) := ⟨fun _ => MeasurableSet.of_discrete⟩

def weight (p0 p1 : ℝ≥0) (z : Fin 2 × Fin 2) : ℝ≥0 :=
  (1/2)*(if z.2=0 then 1-(if z.1=0 then p1 else p0) else (if z.1=0 then p1 else p0))

def finitePathLaw (p0 p1 : ℝ≥0) (h0 : p0 ≤ 1) (h1 : p1 ≤ 1) : PMF (Fin 2 × Fin 2) :=
  PMF.ofFintype (fun z => (weight p0 p1 z : ℝ≥0∞)) (by
    have hw : ∑ z : Fin 2 × Fin 2, weight p0 p1 z=1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_sum]
      simp [weight,Fintype.sum_prod_type,Fin.sum_univ_succ,NNReal.coe_sub h0,NNReal.coe_sub h1]
      ring
    exact_mod_cast hw)

def firstCost (z : Fin 2 × Fin 2) : ℝ := if z.1=0 then 0 else 1
def finalCost (z : Fin 2 × Fin 2) : ℝ := if z.2=0 then 0 else 1
def remainingBudget (z : Fin 2 × Fin 2) : ℝ := (1-firstCost z)/(1/2)
def totalSafetyCost (z : Fin 2 × Fin 2) : ℝ := firstCost z+(1/2)*finalCost z
def finalReward (z : Fin 2 × Fin 2) : ℝ := finalCost z
/-- All histories merge at the same physical decision state. -/
def decisionState (_z : Fin 2 × Fin 2) : Unit := ()

theorem actual_two_stage_joint_probabilities
    (p0 p1 : ℝ≥0) (h0 : p0 ≤ 1) (h1 : p1 ≤ 1) :
    (finitePathLaw p0 p1 h0 h1 (0,0)).toReal=(1-(p1:ℝ))/2 ∧
    (finitePathLaw p0 p1 h0 h1 (0,1)).toReal=(p1:ℝ)/2 ∧
    (finitePathLaw p0 p1 h0 h1 (1,0)).toReal=(1-(p0:ℝ))/2 ∧
    (finitePathLaw p0 p1 h0 h1 (1,1)).toReal=(p0:ℝ)/2 := by
  simp [finitePathLaw,PMF.ofFintype_apply,weight,NNReal.coe_sub h0,NNReal.coe_sub h1,div_eq_mul_inv]

theorem actual_remaining_discounted_budget_and_violation_event
    (z : Fin 2 × Fin 2) :
    remainingBudget z=(if z.1=0 then 2 else 0) ∧
    (1<totalSafetyCost z ↔ z=(1,1)) ∧
    (totalSafetyCost z ≤ 1 ↔ finalCost z ≤ remainingBudget z) := by
  rcases z with ⟨i,a⟩
  fin_cases i <;> fin_cases a <;> norm_num [remainingBudget,firstCost,totalSafetyCost,finalCost]

theorem actual_almost_sure_finite_budget_feasibility_iff_zero_risky_action_at_zero_budget
    (p0 p1 : ℝ≥0) (h0 : p0 ≤ 1) (h1 : p1 ≤ 1) :
    (∀ᵐ z ∂(finitePathLaw p0 p1 h0 h1).toMeasure, totalSafetyCost z ≤ 1) ↔ p0=0 := by
  have hbad : {z : Fin 2 × Fin 2 | ¬totalSafetyCost z ≤ 1}={(1,1)} := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_singleton_iff,not_le]
    exact (actual_remaining_discounted_budget_and_violation_event z).2.1
  rw [ae_iff,hbad,PMF.toMeasure_apply_singleton,finitePathLaw,PMF.ofFintype_apply]
  simp [weight]

theorem actual_finite_path_expected_reward
    (p0 p1 : ℝ≥0) (h0 : p0 ≤ 1) (h1 : p1 ≤ 1) :
    (∫ z, finalReward z ∂(finitePathLaw p0 p1 h0 h1).toMeasure)=((p0:ℝ)+(p1:ℝ))/2 := by
  rw [PMF.integral_eq_sum]
  have hp:=actual_two_stage_joint_probabilities p0 p1 h0 h1
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,finalReward,finalCost,smul_eq_mul,hp.2.1,hp.2.2.2]
  ring

theorem actual_augmented_budget_policy_is_globally_optimal
    (p0 p1 : ℝ≥0) (h0 : p0 ≤ 1) (h1 : p1 ≤ 1)
    (hsafe : ∀ᵐ z ∂(finitePathLaw p0 p1 h0 h1).toMeasure, totalSafetyCost z ≤ 1) :
    (∫ z, finalReward z ∂(finitePathLaw p0 p1 h0 h1).toMeasure) ≤ 1/2 ∧
    (∀ᵐ z ∂(finitePathLaw 0 1 (by norm_num) (by norm_num)).toMeasure, totalSafetyCost z ≤ 1) ∧
    (∫ z, finalReward z ∂(finitePathLaw 0 1 (by norm_num) (by norm_num)).toMeasure)=1/2 := by
  have hz := (actual_almost_sure_finite_budget_feasibility_iff_zero_risky_action_at_zero_budget p0 p1 h0 h1).mp hsafe
  rw [actual_finite_path_expected_reward,hz]
  refine ⟨?_,?_,?_⟩
  · have hh : (p1:ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  · exact (actual_almost_sure_finite_budget_feasibility_iff_zero_risky_action_at_zero_budget 0 1 (by norm_num) (by norm_num)).mpr rfl
  · rw [actual_finite_path_expected_reward]
    norm_num

theorem actual_every_unaugmented_feasible_policy_has_strictly_lower_reward
    (p : ℝ≥0) (hp : p ≤ 1)
    (hsafe : ∀ᵐ z ∂(finitePathLaw p p hp hp).toMeasure, totalSafetyCost z ≤ 1) :
    (∫ z, finalReward z ∂(finitePathLaw p p hp hp).toMeasure)=0 ∧
    (∫ z, finalReward z ∂(finitePathLaw p p hp hp).toMeasure)<
      (∫ z, finalReward z ∂(finitePathLaw 0 1 (by norm_num) (by norm_num)).toMeasure) := by
  have hz := (actual_almost_sure_finite_budget_feasibility_iff_zero_risky_action_at_zero_budget p p hp hp).mp hsafe
  simp [actual_finite_path_expected_reward,hz]

theorem actual_same_physical_state_has_two_distinct_remaining_budgets :
    decisionState (0,0)=decisionState (1,0) ∧ remainingBudget (0,0)=2 ∧ remainingBudget (1,0)=0 ∧
    ¬∃ riskyProbability : Unit → ℝ, riskyProbability (decisionState (0,0))=1 ∧ riskyProbability (decisionState (1,0))=0 := by
  norm_num [decisionState,remainingBudget,firstCost]

end SafeLearning.CompleteSauteRepresentation22
