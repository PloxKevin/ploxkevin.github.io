import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedResidualModels
open Filter
open scoped NNReal

theorem actual_metric_fixed_point_error_is_bounded_by_the_true_residual
    {Space : Type*} [MetricSpace Space] (function : Space → Space) (factor : ℝ≥0)
    (hfactor : factor < 1) (hlipschitz : LipschitzWith factor function)
    (point fixed : Space) (hfixed : function fixed=fixed) :
    dist point fixed ≤ dist point (function point)/(1-(factor:ℝ)) := by
  have htriangle := dist_triangle point (function point) fixed
  have hcontraction := hlipschitz.dist_le_mul point fixed
  rw [hfixed] at hcontraction
  have hreal : (factor:ℝ)<1 := by exact_mod_cast hfactor
  have hpositive : (0:ℝ)<1-factor := sub_pos.mpr hreal
  apply (le_div_iff₀ hpositive).mpr
  nlinarith

def actualEquilibriumLayer (value : ℝ) : ℝ := (1/2)*value+2

theorem actual_equilibrium_layer_has_unique_fixed_point_four (value : ℝ) :
    actualEquilibriumLayer value=value ↔ value=4 := by
  unfold actualEquilibriumLayer
  constructor <;> intro h <;> linarith

theorem actual_equilibrium_layer_is_a_half_contraction :
    LipschitzWith (1/2) actualEquilibriumLayer := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [Real.dist_eq,Real.dist_eq]
  have he : actualEquilibriumLayer first-actualEquilibriumLayer second=(1/2)*(first-second) := by
    unfold actualEquilibriumLayer
    ring
  rw [he,abs_mul]
  norm_num

theorem actual_source_first_three_iterates_and_residual :
    actualEquilibriumLayer^[1] 0=2 ∧ actualEquilibriumLayer^[2] 0=3 ∧
      actualEquilibriumLayer^[3] 0=7/2 ∧ actualEquilibriumLayer (7/2)=15/4 ∧
      |actualEquilibriumLayer (7/2)-(7/2)|=1/4 := by
  norm_num [Function.iterate_succ_apply',actualEquilibriumLayer]

theorem actual_source_residual_certifies_half_error_and_the_bound_is_attained :
    |(7/2:ℝ)-4| ≤ |actualEquilibriumLayer (7/2)-(7/2)|/(1-(1/2)) ∧
      |(7/2:ℝ)-4|=1/2 ∧
      |actualEquilibriumLayer (7/2)-(7/2)|/(1-(1/2))=1/2 := by
  have hb := actual_metric_fixed_point_error_is_bounded_by_the_true_residual
    actualEquilibriumLayer (1/2) (by norm_num)
    actual_equilibrium_layer_is_a_half_contraction (7/2) 4
    (by norm_num [actualEquilibriumLayer])
  norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hb
  constructor
  · simpa only [Real.dist_eq,abs_sub_comm (7/2) (actualEquilibriumLayer (7/2)),
      show (1:ℝ)-(1/2)=1/2 by norm_num] using hb
  · norm_num [actualEquilibriumLayer]

theorem actual_equilibrium_layer_iterates_have_the_true_geometric_formula
    (initial : ℝ) (steps : ℕ) :
    actualEquilibriumLayer^[steps] initial=4+(1/2:ℝ)^steps*(initial-4) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    rw [Function.iterate_succ_apply',ih,pow_succ]
    unfold actualEquilibriumLayer
    ring

theorem actual_equilibrium_layer_iteration_converges_from_every_initial (initial : ℝ) :
    Tendsto (fun steps : ℕ => actualEquilibriumLayer^[steps] initial) atTop (nhds 4) := by
  simp only [actual_equilibrium_layer_iterates_have_the_true_geometric_formula]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)
  convert tendsto_const_nhds.add (hp.mul_const (initial-4)) using 1
  norm_num

end SafeLearning.CompleteAppliedResidualModels
