import SafeLearning.CompletePolicyFOCOPSHard20
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompletePolicyFOCOPSTight20
open SafeLearning.CompletePolicyFOCOPSModel20
open SafeLearning.CompletePolicyFOCOPSNumbers20
open SafeLearning.CompletePolicyFOCOPSHard20
open SafeLearning.CompleteAppliedTemperatureSoftmax

def inverseTemperature (p : ℝ) : ℝ := 2 / Real.log (p/(1-p))
def positiveTemperatureDual (delta lam ν : ℝ) : ℝ :=
  lam*delta+lam*Real.log (Real.cosh ((1-2*ν)/lam))+ν/2

theorem actual_inverse_temperature_positive (p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) 1) :
    0 < inverseTemperature p := by
  apply div_pos (by norm_num)
  apply Real.log_pos
  rw [one_lt_div (by linarith [hp.2])]
  linarith [hp.1]

theorem actual_inverse_temperature_gibbs_mass (p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) 1) :
    probability (inverseTemperature p) 0=p := by
  have hprob:=actual_gibbs_probability_in_open_unit_interval (inverseTemperature p) 0
  have hp0 : 0<p := by linarith [hp.1]
  have hp1 : 0<1-p := by linarith [hp.2]
  have hl : 0<Real.log (p/(1-p)) := by
    apply Real.log_pos;rw [one_lt_div hp1];linarith [hp.1]
  have he : Real.log (probability (inverseTemperature p) 0 /
      (1-probability (inverseTemperature p) 0))=Real.log (p/(1-p)) := by
    rw [actual_gibbs_log_odds]
    dsimp [inverseTemperature]
    field_simp
    norm_num
  have hr := Real.log_injOn_pos (div_pos hprob.1 (by linarith [hprob.2]))
    (div_pos hp0 hp1) he
  have hz : 1-probability (inverseTemperature p) 0≠0 := by linarith [hprob.2]
  field_simp [hz,hp1.ne'] at hr
  nlinarith

theorem interior_unit_membership (p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) 1) :
    p∈Set.Icc (0:ℝ) 1 := by
  constructor <;> linarith [hp.1,hp.2]

theorem actual_inverse_temperature_gibbs_is_the_binary_law
    (p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) 1) :
    gibbs (inverseTemperature p) 0=binaryLaw p (interior_unit_membership p hp) := by
  apply PMF.ext
  intro i
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  fin_cases i
  · change (gibbs (inverseTemperature p) 0 0).toReal = (binaryLaw p (interior_unit_membership p hp) 0).toReal
    rw [(actual_gibbs_masses _ _).1,(actual_binary_law_masses _ _).1]
    exact actual_inverse_temperature_gibbs_mass p hp
  · change (gibbs (inverseTemperature p) 0 1).toReal = (binaryLaw p (interior_unit_membership p hp) 1).toReal
    rw [(actual_gibbs_masses _ _).2,(actual_binary_law_masses _ _).2,
      actual_inverse_temperature_gibbs_mass p hp]

theorem actual_positive_temperature_dual_is_attained_global_supremum
    (delta lam ν : ℝ) (hlam : 0<lam) (law : PMF (Fin 2)) :
    hardLagrangian delta lam ν law≤positiveTemperatureDual delta lam ν ∧
      hardLagrangian delta lam ν (gibbs lam ν)=positiveTemperatureDual delta lam ν := by
  have h:=actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
    (scores ν) lam hlam law
  have hg:=actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
    (scores ν) lam hlam (gibbs lam ν)
  have he:=hg.2.mpr rfl
  have hv : actualTemperatureValue (scores ν) lam-lam*Real.log 2+ν/2+lam*delta=
      positiveTemperatureDual delta lam ν := by
    have hs : actualPartition (scores ν) lam=2*Real.cosh ((1-2*ν)/lam) := by
      have he : (2*ν-1)/lam = -((1-2*ν)/lam) := by ring
      simp [actualPartition,scores,Fin.sum_univ_two,Real.cosh_eq,he]
      ring
    rw [actualTemperatureValue,hs,Real.log_mul (by norm_num : (2:ℝ)≠0)
      (Real.cosh_pos _).ne']
    dsimp [positiveTemperatureDual]
    ring
  constructor
  · rw [hardLagrangian,actual_lagrangian_is_entropy_objective,← hv]
    linarith [h.1]
  · rw [hardLagrangian,actual_lagrangian_is_entropy_objective,he,hv]

theorem actual_any_interior_KL_root_gives_unique_hard_optimizer
    (delta p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) (5/8))
    (hroot : binaryKLExpression p=delta)
    (law : PMF (Fin 2)) (hf : hardFeasible delta law) :
    reward law≤2*p-1 ∧
      (reward law=2*p-1 ↔ law=gibbs (inverseTemperature p) 0) ∧
      positiveTemperatureDual delta (inverseTemperature p) 0=2*p-1 := by
  have hp1 : p∈Set.Ioo (1/2:ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have ht:=actual_inverse_temperature_positive p hp1
  have hg:=actual_inverse_temperature_gibbs_mass p hp1
  have hr : reward (gibbs (inverseTemperature p) 0)=2*p-1 := by
    rw [(actual_reward_and_cost_expectations _).1,(actual_gibbs_masses _ _).1,hg]
  have hk : trueKL (gibbs (inverseTemperature p) 0)=delta := by
    rw [actual_inverse_temperature_gibbs_is_the_binary_law p hp1,
      actual_binary_law_true_KL,hroot]
  have hm:=actual_gibbs_is_unique_global_lagrangian_maximizer (inverseTemperature p) 0 ht law
  have hb:=actual_hard_weak_duality delta (inverseTemperature p) 0 ht.le (by norm_num) law hf
  have hv : hardLagrangian delta (inverseTemperature p) 0
      (gibbs (inverseTemperature p) 0)=2*p-1 := by
    dsimp [hardLagrangian,lagrangian,regularizedReward];rw [hr,hk];ring
  have hmax : hardLagrangian delta (inverseTemperature p) 0 law≤2*p-1 := by
    unfold hardLagrangian at hv ⊢
    linarith [hm.1]
  refine ⟨by linarith,?_,?_⟩
  · constructor
    · intro he
      apply hm.2.mp
      unfold hardLagrangian at hb hmax hv
      linarith
    · intro he;rw [he,hr]
  · rw [← (actual_positive_temperature_dual_is_attained_global_supremum
      delta (inverseTemperature p) 0 ht law).2,hv]

theorem actual_tight_KL_root_is_strictly_interior
    (p : ℝ) (hp : p∈Set.Icc (1/2:ℝ) (5/8)) (he : binaryKLExpression p=1/50) :
    p∈Set.Ioo (1/2:ℝ) (5/8) := by
  have hl : binaryKLExpression (1/2)=0 := by norm_num [binaryKLExpression]
  have hh:=actual_five_eighths_kl_enclosure_and_both_budget_comparisons.2.2.1
  constructor
  · exact lt_of_le_of_ne hp.1 (by intro h;rw [← h,hl] at he;norm_num at he)
  · exact lt_of_le_of_ne hp.2 (by intro h;rw [h] at he;linarith)

end SafeLearning.CompletePolicyFOCOPSTight20
