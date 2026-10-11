import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteLyapunovScenarioGenericLog26

/-- The literal one-variable scenario tail inequality has its exact logarithmic
threshold for arbitrary admissible violation and confidence parameters. -/
theorem actual_generic_one_dimensional_scenario_logarithmic_threshold
    (epsilon beta : ℝ) (he : 0<epsilon ∧ epsilon<1)
    (hb : 0<beta ∧ beta<1) (n : ℕ) :
    (1-epsilon)^n≤beta ↔
      Real.log (1/beta)/(-Real.log (1-epsilon))≤(n:ℝ) := by
  have hpos : 0<1-epsilon := sub_pos.mpr he.2
  have hlt : 1-epsilon<1 := sub_lt_self 1 he.1
  have hden : 0< -Real.log (1-epsilon) := neg_pos.mpr (Real.log_neg hpos hlt)
  have hlog : Real.log beta = -Real.log (1/beta) := by
    rw [one_div,Real.log_inv,neg_neg]
  rw [←Real.log_le_log_iff (pow_pos hpos n) hb.1,
    Real.log_pow,hlog,div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith

end SafeLearning.CompleteLyapunovScenarioGenericLog26
