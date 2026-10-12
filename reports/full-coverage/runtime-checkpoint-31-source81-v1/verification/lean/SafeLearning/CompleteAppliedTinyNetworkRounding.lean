import SafeLearning.CompleteAppliedTinyNetworkSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTinyNetworkRounding

theorem actual_local_certificate_gain_factor_has_the_nearest_two_decimal_rounding :
    |Real.sqrt 10-(79/25:ℝ)|≤1/200 ∧ (79/25:ℝ)<Real.sqrt 10 := by
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg 10
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · nlinarith

end SafeLearning.CompleteAppliedTinyNetworkRounding
