import SafeLearning.CompleteModulesGoSafeToyFeasibility
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology
namespace SafeLearning.CompleteModulesGoSafeToyBetweenGrid
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility

theorem actual_source_margin_has_the_true_between_grid_derivative :
    HasDerivAt (actualSourceSafety 8) (128*Real.pi/45) (1/8:ℝ) := by
  have hangle : 4*Real.pi*(1/8)=Real.pi/2 := by ring
  have hc : HasDerivAt (fun a : ℝ => Real.cos (4*Real.pi*a)) (-4*Real.pi) (1/8:ℝ) := by
    have hh := (Real.hasDerivAt_cos (4*Real.pi*(1/8))).comp (1/8:ℝ)
      ((hasDerivAt_id (1/8:ℝ)).const_mul (4*Real.pi))
    simp only [mul_one] at hh
    change HasDerivAt (fun a : ℝ => Real.cos (4*Real.pi*a))
      (-Real.sin (4*Real.pi*(1/8))*(4*Real.pi)) (1/8:ℝ) at hh
    rw [hangle,Real.sin_pi_div_two] at hh
    simpa using hh
  have hq := (((((hasDerivAt_const (1/8:ℝ) (1:ℝ)).add hc).const_mul (4/5)).const_mul 8).add_const (3/5)).div_const 9
  have hh := (hasDerivAt_const (1/8:ℝ) (1:ℝ)).sub hq
  have hfun : (fun a : ℝ => 1-(8*((4/5)*(1+Real.cos (4*Real.pi*a)))+3/5)/9)=actualSourceSafety 8 := by
    funext a
    rw [actual_source_zero_start_safety_is_the_true_equilibrium_margin 8 a (by norm_num)]
    norm_num [actualEquilibrium,actualReference]
  change HasDerivAt (fun a : ℝ => 1-(8*((4/5)*(1+Real.cos (4*Real.pi*a)))+3/5)/9)
    (0-(8*((4/5)*(0+(-4*Real.pi))))/9) (1/8:ℝ) at hh
  rw [hfun] at hh
  convert hh using 1 <;> ring

theorem actual_between_grid_slope_exceeds_the_printed_grid_constant :
    (128/15:ℝ) < 128*Real.pi/45 := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

theorem actual_printed_grid_constant_does_not_bound_the_source_on_the_continuous_parameter_interval :
    ¬LipschitzOnWith (⟨128/15,by norm_num⟩ : NNReal) (actualSourceSafety 8) (Icc (0:ℝ) 1) := by
  intro h
  have hnhds : Icc (0:ℝ) 1 ∈ 𝓝 (1/8:ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hn := norm_deriv_le_of_lipschitzOn hnhds h
  rw [actual_source_margin_has_the_true_between_grid_derivative.deriv] at hn
  have hp : 0 ≤ 128*Real.pi/45 := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hp] at hn
  exact not_le_of_gt actual_between_grid_slope_exceeds_the_printed_grid_constant hn

end SafeLearning.CompleteModulesGoSafeToyBetweenGrid
