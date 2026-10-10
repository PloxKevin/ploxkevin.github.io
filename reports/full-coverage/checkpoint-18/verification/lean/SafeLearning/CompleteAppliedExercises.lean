import Mathlib
import SafeLearning.CompleteAppliedProbability
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedExercises
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedProbability
open scoped ENNReal NNReal Topology

def chainTransition (state : Fin 2) : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((if state=0 then (![(4/5:ℝ≥0),1/5] : Fin 2 → ℝ≥0) i
    else (![(3/10:ℝ≥0),7/10] : Fin 2 → ℝ≥0) i) : ℝ≥0∞))
  (by split_ifs <;> norm_cast <;> norm_num [Fin.sum_univ_succ])

def chainOne : PMF (Fin 2) := (PMF.pure 0).bind chainTransition
def chainTwo : PMF (Fin 2) := chainOne.bind chainTransition
def chainStationary : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(3/5:ℝ≥0),2/5] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])

theorem chain_one_values : (chainOne 0).toReal=4/5 ∧ (chainOne 1).toReal=1/5 := by
  norm_num [chainOne,chainTransition,PMF.bind_pure]

theorem chain_two_values : (chainTwo 0).toReal=7/10 ∧ (chainTwo 1).toReal=3/10 := by
  norm_num [chainTwo,chainOne,chainTransition,PMF.bind_pure,PMF.bind_apply,
    tsum_fintype,Fin.sum_univ_succ]
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add]
  all_goals norm_num

theorem chain_stationary_preserved : chainStationary.bind chainTransition=chainStationary := by
  ext i
  fin_cases i <;> norm_num [PMF.bind_apply,chainStationary,chainTransition,
    tsum_fintype,Fin.sum_univ_succ]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv]
  all_goals norm_num

theorem chain_stationary_unique (a : ℝ) :
    (4/5)*a+(3/10)*(1-a)=a ↔ a=3/5 := by
  constructor <;> intro h <;> linarith

theorem chain_stationary_moves : (chainTransition 0 1).toReal=1/5 ∧
    (chainStationary 0).toReal=3/5 ∧ (chainStationary 1).toReal=2/5 := by
  norm_num [chainTransition,chainStationary]

theorem complement_ready {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    (hA : MeasurableSet A) (hp : μ.real A=3/20) : μ.real Aᶜ=17/20 := by
  rw [complement_probability μ A hA,hp]
  norm_num

def regretMeans : Fin 3 → ℝ := ![4/5,3/5,3/10]
def regretActions : Fin 4 → Fin 3 := ![0,1,2,1]
def cumulativeRegret : ℝ := ∑ t : Fin 4, (4/5-regretMeans (regretActions t))

theorem regret_values : cumulativeRegret=9/10 ∧ cumulativeRegret/4=9/40 ∧
    4/5-regretMeans 2=1/2 := by
  norm_num [cumulativeRegret,regretMeans,regretActions,Fin.sum_univ_succ]

def staticRoundReward (arm time : Fin 2) : ℝ := if arm=time then 1 else 0

theorem comparator_values :
    (∑ t : Fin 2, staticRoundReward 0 t)=1 ∧
    (∀ a : Fin 2, (∑ t : Fin 2, staticRoundReward a t)=1) ∧
    (∑ t : Fin 2, staticRoundReward t t)=2 ∧ (1-1:ℝ)=0 ∧ (2-1:ℝ)=1 := by
  norm_num [staticRoundReward,Fin.sum_univ_succ]

theorem optimistic_and_safe (f1 f2 : ℝ)
    (h1 : |f1-3/10|≤2/5) (h2 : |f2-1/5|≤1/10) :
    (1/2+1/5:ℝ)>(3/5+1/20) ∧ 0≤f2 ∧
    (∃ f : ℝ, |f-3/10|≤2/5 ∧ 0<f) ∧
    (∃ f : ℝ, |f-3/10|≤2/5 ∧ f<0) := by
  have h := abs_le.mp h2
  refine ⟨by norm_num,by linarith,?_,?_⟩
  · exact ⟨3/10,by norm_num,by norm_num⟩
  · exact ⟨-1/10,by norm_num,by norm_num⟩

def finiteTrajectoryReward (n : ℕ) : ℝ := if n=0 then 2 else if n=1 then 4 else 0

theorem short_return :
    (∑' n : ℕ, (1/2:ℝ)^n*finiteTrajectoryReward n)=4 ∧
    (∑' n : ℕ, (1/2:ℝ)^n*finiteTrajectoryReward (n+1))=4 := by
  have h0 : (fun n : ℕ => (1/2:ℝ)^n*finiteTrajectoryReward n)=
      (fun n => if n ∈ ({0,1} : Finset ℕ) then (1/2:ℝ)^n*finiteTrajectoryReward n else 0) := by
    ext n
    by_cases hn0 : n=0
    · subst n; simp
    by_cases hn1 : n=1
    · subst n; simp
    simp [hn0,hn1,finiteTrajectoryReward]
  have h1 : (fun n : ℕ => (1/2:ℝ)^n*finiteTrajectoryReward (n+1))=
      (fun n => if n ∈ ({0} : Finset ℕ) then (1/2:ℝ)^n*finiteTrajectoryReward (n+1) else 0) := by
    ext n; by_cases hn : n=0
    · subst n; simp
    · have hn1 : n+1≠1 := by omega
      simp [hn,hn1,finiteTrajectoryReward]
  rw [h0,h1]
  constructor
  · rw [tsum_eq_sum (s := ({0,1} : Finset ℕ)) (by intro n hn;simp [hn])]
    norm_num [finiteTrajectoryReward]
  · rw [tsum_eq_sum (s := ({0} : Finset ℕ)) (by intro n hn;simp [hn])]
    norm_num [finiteTrajectoryReward]

def continuationLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(3/4:ℝ≥0),1/4] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def actionLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(3/5:ℝ≥0),2/5] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def continuationValues : Fin 2 → ℝ := ![4,0]
def actionValues : Fin 2 → ℝ := ![1+(1/2)*finiteExpectation continuationLaw continuationValues,1]

theorem transition_and_action_expectations :
    finiteExpectation continuationLaw continuationValues=3 ∧ actionValues 0=5/2 ∧
    finiteExpectation actionLaw actionValues=19/10 := by
  norm_num [finiteExpectation,continuationLaw,actionLaw,continuationValues,actionValues,
    Fin.sum_univ_succ]

def rareFailureLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(1/100:ℝ≥0),99/100] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def rareViolationCount : Fin 2 → ℝ := ![100,0]

theorem equal_expected_cost_distinct_failure :
    finiteExpectation rareFailureLaw rareViolationCount=1 ∧
    eventProbability rareFailureLaw {i | 0<rareViolationCount i}=1/100 ∧
    finiteExpectation (PMF.pure (0:Fin 2)) (fun _ => 1)=1 ∧
    eventProbability (PMF.pure (0:Fin 2)) {i | (0:ℝ)<1}=1 := by
  norm_num [finiteExpectation,rareFailureLaw,rareViolationCount,eventProbability,
    PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,Fin.sum_univ_succ,
    PMF.pure_apply,Set.indicator]

theorem one_state_bellman_unique (v : ℝ) : v=2+(1/2)*v ↔ v=4 := by
  constructor <;> intro h <;> linarith

theorem cycle_bellman_unique (a b : ℝ) :
    (a=1+(1/2)*b ∧ b=(1/2)*a) ↔ (a=4/3 ∧ b=2/3) := by
  constructor
  · rintro ⟨ha,hb⟩; constructor <;> linarith
  · rintro ⟨rfl,rfl⟩; norm_num

theorem cycle_advantage : (0+(1/2:ℝ)*(4/3))-(4/3)=-2/3 := by norm_num

def halfValueIteration : ℕ → ℝ
  | 0 => 0
  | n+1 => max (1+(1/2)*halfValueIteration n) (2+(1/2)*halfValueIteration n)

theorem half_value_iteration_formula (n : ℕ) :
    halfValueIteration n=4*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp [halfValueIteration]
  | succ n ih => rw [halfValueIteration,ih,max_eq_right (by linarith)]; ring

theorem half_value_iteration_values : halfValueIteration 1=2 ∧
    halfValueIteration 2=3 ∧ halfValueIteration 3=7/2 := by
  norm_num [halfValueIteration]

theorem half_value_iteration_converges : Tendsto halfValueIteration atTop (𝓝 4) := by
  change Tendsto (fun n => halfValueIteration n) atTop (𝓝 4)
  simp_rw [half_value_iteration_formula]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hp).const_mul 4

theorem q_learning_update :
    (1+(9/10:ℝ)*2)=14/5 ∧ (14/5:ℝ)-1/2=23/10 ∧
    (1/2:ℝ)+(1/5)*(23/10)=24/25 ∧ (1/2:ℝ)+(1/5)*(1-1/2)=3/5 := by
  norm_num

def affineRelu (x : Fin 2 → ℝ) : ℝ := max 0 (2*x 0-x 1+1/2)

theorem affine_relu_examples :
    (2*(1:ℝ)-3+1/2)=-1/2 ∧ affineRelu ![1,3]=0 ∧
    (2*(2:ℝ)-1+1/2)=7/2 ∧ affineRelu ![2,1]=7/2 := by
  norm_num [affineRelu]

def correlationMatrix : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1,-1,0,0;0,1,-1,0;0,0,1,-1]

theorem correlation_matrix_output : correlationMatrix.mulVec ![1,2,3,4]=![-1,-1,-1] := by
  ext i; fin_cases i <;> norm_num [correlationMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

end SafeLearning.CompleteAppliedExercises
