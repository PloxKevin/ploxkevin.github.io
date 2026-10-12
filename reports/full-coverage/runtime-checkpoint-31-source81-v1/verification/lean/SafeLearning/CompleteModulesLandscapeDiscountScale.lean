import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeDiscountScale

theorem actual_time_constant_has_the_source_geometric_discount (tau : ℝ) (htau : 0<tau) :
    0<Real.exp (-1/tau) ∧ Real.exp (-1/tau)<1 := by
  refine ⟨Real.exp_pos _,?_⟩
  exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) htau)

theorem actual_delayed_geometric_factor_equals_the_source_exponential (tau : ℝ) (delay : ℕ) :
    (Real.exp (-1/tau))^delay=Real.exp (-(delay:ℝ)/tau) := by
  rw [←Real.exp_nat_mul]
  congr 1
  ring

theorem actual_inverse_failure_discount_is_the_growing_exponential (tau : ℝ) (delay : ℕ) :
    ((Real.exp (-1/tau))^delay)⁻¹=Real.exp ((delay:ℝ)/tau) := by
  rw [actual_delayed_geometric_factor_equals_the_source_exponential,←Real.exp_neg]
  congr 1
  ring

theorem actual_penalty_needed_for_a_fixed_discounted_charge_has_the_source_exponential_scale
    (tau charge penalty : ℝ) (delay : ℕ) :
    charge≤ penalty*(Real.exp (-1/tau))^delay ↔ charge*Real.exp ((delay:ℝ)/tau)≤ penalty := by
  have hpos : 0<(Real.exp (-1/tau))^delay := pow_pos (Real.exp_pos _) _
  rw [←div_le_iff₀ hpos,div_eq_mul_inv,actual_inverse_failure_discount_is_the_growing_exponential]

theorem actual_required_penalty_scale_is_monotone_in_failure_delay
    (tau charge : ℝ) (htau : 0<tau) (hcharge : 0≤ charge) :
    Monotone (fun delay : ℕ=>charge*Real.exp ((delay:ℝ)/tau)) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ hcharge
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) htau.le

end SafeLearning.CompleteModulesLandscapeDiscountScale
