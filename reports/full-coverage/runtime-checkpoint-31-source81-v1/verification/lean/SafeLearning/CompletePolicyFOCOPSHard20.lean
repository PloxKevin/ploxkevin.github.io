import SafeLearning.CompletePolicyFOCOPSModel20
import SafeLearning.CompletePolicyFOCOPSNumbers20
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompletePolicyFOCOPSHard20
open SafeLearning.CompletePolicyFOCOPSModel20
open SafeLearning.CompletePolicyFOCOPSNumbers20

def binaryLaw (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : PMF (Fin 2) :=
  PMF.ofFintype (fun i => if i=0 then ENNReal.ofReal p else ENNReal.ofReal (1-p))
    (by simp only [Fin.sum_univ_two];norm_num;rw [← ENNReal.ofReal_add hp.1 (by linarith [hp.2])];norm_num)

theorem actual_binary_law_masses (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (binaryLaw p hp 0).toReal=p ∧ (binaryLaw p hp 1).toReal=1-p := by
  simp [binaryLaw,ENNReal.toReal_ofReal,hp.1,show 0≤1-p by linarith [hp.2]]

theorem actual_binary_law_true_KL (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    trueKL (binaryLaw p hp)=binaryKLExpression p := by
  rw [trueKL,oldLaw,actual_any_two_action_policy_true_uniform_kl,
    (actual_binary_law_masses p hp).1]

def hardFeasible (delta : ℝ) (law : PMF (Fin 2)) : Prop :=
  trueKL law≤delta ∧ cost law≤1/2
def hardLagrangian (delta lam ν : ℝ) (law : PMF (Fin 2)) : ℝ :=
  lagrangian lam ν law+lam*delta

theorem actual_hard_weak_duality (delta lam ν : ℝ) (hlam : 0≤lam) (hν : 0≤ν)
    (law : PMF (Fin 2)) (hf : hardFeasible delta law) :
    reward law≤hardLagrangian delta lam ν law := by
  have hk : 0≤lam*(delta-trueKL law) := mul_nonneg hlam (sub_nonneg.mpr hf.1)
  have hc : 0≤ν*(1/2-cost law) := mul_nonneg hν (sub_nonneg.mpr hf.2)
  dsimp [hardLagrangian,lagrangian,regularizedReward]
  nlinarith

theorem actual_zero_temperature_half_price_dual_is_constant (delta : ℝ)
    (law : PMF (Fin 2)) : hardLagrangian delta 0 (1/2) law=1/4 := by
  have h:=actual_reward_and_cost_expectations law
  dsimp [hardLagrangian,lagrangian,regularizedReward]
  rw [h.1,h.2]
  ring

theorem actual_wide_budget_policy_feasible :
    hardFeasible (1/20) (binaryLaw (5/8) (by norm_num : (5/8:ℝ)∈Set.Icc (0:ℝ) 1)) := by
  constructor
  · rw [actual_binary_law_true_KL]
    exact actual_five_eighths_kl_enclosure_and_both_budget_comparisons.2.2.2.le
  · rw [actual_cost_feasibility_iff,(actual_binary_law_masses _ _).1]

theorem actual_wide_budget_primal_and_dual_optimum
    (law : PMF (Fin 2)) (hf : hardFeasible (1/20) law) :
    reward law≤1/4 ∧
      reward (binaryLaw (5/8) (by norm_num : (5/8:ℝ)∈Set.Icc (0:ℝ) 1))=1/4 ∧
      hardLagrangian (1/20) 0 (1/2) law=1/4 := by
  refine ⟨?_,?_,actual_zero_temperature_half_price_dual_is_constant _ _⟩
  · have h:=actual_hard_weak_duality (1/20) 0 (1/2) (by norm_num) (by norm_num) law hf
    rwa [actual_zero_temperature_half_price_dual_is_constant] at h
  · rw [(actual_reward_and_cost_expectations _).1,(actual_binary_law_masses _ _).1]
    norm_num

theorem actual_wide_budget_other_nonnegative_dual_parameters_bound
    (lam ν : ℝ) (hlam : 0≤lam) (hν : 0≤ν) :
    (1/4:ℝ)≤hardLagrangian (1/20) lam ν
      (binaryLaw (5/8) (by norm_num : (5/8:ℝ)∈Set.Icc (0:ℝ) 1)) := by
  have h:=actual_hard_weak_duality (1/20) lam ν hlam hν _ actual_wide_budget_policy_feasible
  rw [(actual_reward_and_cost_expectations _).1,(actual_binary_law_masses _ _).1] at h
  norm_num at h ⊢
  exact h

theorem actual_binary_KL_continuous_on_open_unit_interval :
    ContinuousOn binaryKLExpression (Set.Ioo (0:ℝ) 1) := by
  intro p hp
  have h0 : 2*p≠0 := by nlinarith [hp.1]
  have h1 : 2*(1-p)≠0 := by nlinarith [hp.2]
  exact (((continuousAt_id.mul
    ((continuousAt_const.mul continuousAt_id).log h0)).add
      ((continuousAt_const.sub continuousAt_id).mul
        ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).log h1))).continuousWithinAt)

theorem actual_binary_KL_derivative (p : ℝ) (hp : p∈Set.Ioo (0:ℝ) 1) :
    HasDerivAt binaryKLExpression (Real.log (p/(1-p))) p := by
  have h0 : 2*p≠0 := by nlinarith [hp.1]
  have h1 : 2*(1-p)≠0 := by nlinarith [hp.2]
  have hd:=((hasDerivAt_id p).mul
    (((hasDerivAt_id p).const_mul 2).log h0)).add
      (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul
        ((((hasDerivAt_const p 1).sub (hasDerivAt_id p)).const_mul 2).log h1))
  convert hd using 1
  · funext y;dsimp [binaryKLExpression]
  · dsimp only [id,Pi.sub_apply]
    rw [Real.log_div (ne_of_gt hp.1) (show 1-p≠0 by linarith [hp.2])]
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hp.1),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (show 1-p≠0 by linarith [hp.2])]
    field_simp [ne_of_gt hp.1,show 1-p≠0 by linarith [hp.2]]
    ring

theorem actual_binary_KL_strictly_increasing_above_half :
    StrictMonoOn binaryKLExpression (Set.Icc (1/2:ℝ) (5/8)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f':=fun p=>Real.log (p/(1-p)))
    (convex_Icc _ _)
  · exact actual_binary_KL_continuous_on_open_unit_interval.mono (by
      intro p hp;constructor <;> linarith [hp.1,hp.2])
  · intro p hp;rw [interior_Icc] at hp
    exact (actual_binary_KL_derivative p (by constructor <;> linarith [hp.1,hp.2])).hasDerivWithinAt
  · intro p hp;rw [interior_Icc] at hp
    apply Real.log_pos
    rw [one_lt_div (by linarith [hp.2])]
    linarith [hp.1]

theorem actual_tight_budget_has_unique_interior_KL_root :
    ∃! p : ℝ, p∈Set.Icc (1/2:ℝ) (5/8) ∧ binaryKLExpression p=1/50 := by
  have hlow : binaryKLExpression (1/2)=0 := by norm_num [binaryKLExpression]
  have hhi := actual_five_eighths_kl_enclosure_and_both_budget_comparisons.2.2.1
  have hm : (1/50:ℝ)∈Set.Icc (binaryKLExpression (1/2)) (binaryKLExpression (5/8)) := by
    rw [hlow];constructor;norm_num;exact hhi.le
  obtain ⟨p,hp,he⟩:=intermediate_value_Icc (by norm_num : (1/2:ℝ)≤5/8)
    (actual_binary_KL_continuous_on_open_unit_interval.mono (by
      intro p hp;constructor <;> linarith [hp.1,hp.2])) hm
  refine ⟨p,⟨hp,he⟩,?_⟩
  intro q hq
  exact actual_binary_KL_strictly_increasing_above_half.injOn hq.1 hp (hq.2.trans he.symm)

end SafeLearning.CompletePolicyFOCOPSHard20
