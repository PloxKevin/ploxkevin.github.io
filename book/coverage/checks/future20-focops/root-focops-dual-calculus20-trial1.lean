import SafeLearning.CompletePolicyFOCOPSTight20
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace SafeLearning.CompletePolicyFOCOPSDualCalculus20
open SafeLearning.CompletePolicyFOCOPSModel20
open SafeLearning.CompletePolicyFOCOPSNumbers20
open SafeLearning.CompletePolicyFOCOPSHard20
open SafeLearning.CompletePolicyFOCOPSTight20

theorem actual_interior_root_gibbs_is_feasible_and_cost_strictly_slack
    (delta p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) (5/8))
    (hroot : binaryKLExpression p=delta) :
    trueKL (gibbs (inverseTemperature p) 0)=delta ∧
      cost (gibbs (inverseTemperature p) 0)<1/2 ∧
      hardFeasible delta (gibbs (inverseTemperature p) 0) := by
  have hp1 : p∈Set.Ioo (1/2:ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hg:=actual_inverse_temperature_gibbs_mass p hp1
  have hk : trueKL (gibbs (inverseTemperature p) 0)=delta := by
    rw [actual_inverse_temperature_gibbs_is_the_binary_law p hp1,
      actual_binary_law_true_KL,hroot]
  have hc : cost (gibbs (inverseTemperature p) 0)<1/2 := by
    rw [(actual_reward_and_cost_expectations _).2,(actual_gibbs_masses _ _).1,hg]
    linarith [hp.2]
  exact ⟨hk,hc,⟨hk.le,hc.le⟩⟩

theorem actual_interior_KL_root_dual_global_minimum
    (delta p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) (5/8))
    (hroot : binaryKLExpression p=delta)
    (lam ν : ℝ) (hlam : 0 < lam) (hν : 0≤ν) :
    positiveTemperatureDual delta (inverseTemperature p) 0≤
      positiveTemperatureDual delta lam ν := by
  have hf:=(actual_interior_root_gibbs_is_feasible_and_cost_strictly_slack delta p hp hroot).2.2
  have ho:=actual_any_interior_KL_root_gives_unique_hard_optimizer delta p hp hroot _ hf
  have hr:=actual_hard_weak_duality delta lam ν hlam.le hν _ hf
  have hd:=actual_positive_temperature_dual_is_attained_global_supremum delta lam ν hlam
    (gibbs (inverseTemperature p) 0)
  rw [ho.2.2]
  have he:=ho.2.1.mpr rfl
  linarith [hd.1]

theorem actual_unpriced_dual_derivative (delta lam : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t=>positiveTemperatureDual delta t 0)
      (delta+Real.log (Real.cosh (1/lam))-Real.tanh (1/lam)/lam) lam := by
  have hi:HasDerivAt (fun t:ℝ=>1/t) (-1/lam^2) lam := by
    convert (hasDerivAt_const lam (1:ℝ)).div (hasDerivAt_id lam) hlam.ne' using 1 <;> ring
  have hd:=((hasDerivAt_id lam).mul_const delta).add
    ((hasDerivAt_id lam).mul (hi.cosh.log (Real.cosh_pos _).ne'))
  convert hd using 1
  · funext t;dsimp [positiveTemperatureDual];ring
  · dsimp only [id]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hlam.ne',(Real.cosh_pos (1/lam)).ne']
    ring

theorem actual_interior_root_unpriced_dual_derivative_vanishes
    (delta p : ℝ) (hp : p∈Set.Ioo (1/2:ℝ) (5/8))
    (hroot : binaryKLExpression p=delta) :
    delta+Real.log (Real.cosh (1/inverseTemperature p))-
      Real.tanh (1/inverseTemperature p)/inverseTemperature p=0 := by
  have ht:=actual_inverse_temperature_positive p ⟨hp.1,by linarith [hp.2]⟩
  have hm:IsLocalMin (fun t=>positiveTemperatureDual delta t 0) (inverseTemperature p) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with t ht'
    exact actual_interior_KL_root_dual_global_minimum delta p hp hroot t 0 ht' (by norm_num)
  exact hm.hasDerivAt_eq_zero (actual_unpriced_dual_derivative delta (inverseTemperature p) ht)

end SafeLearning.CompletePolicyFOCOPSDualCalculus20
