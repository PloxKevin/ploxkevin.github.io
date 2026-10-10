import SafeLearning.CompleteAppliedScalarODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedContinuousDiscreteContrast
open CompleteAppliedScalarODE

theorem actual_negative_source_mode_has_the_continuous_ODE (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp ((-6/5:ℝ)*s))
      ((-6/5:ℝ)*Real.exp ((-6/5:ℝ)*t)) t := by
  have h := actual_linear_solution_ODE (-6/5) 1 t
  change HasDerivAt (fun s : ℝ => 1*Real.exp ((-6/5:ℝ)*s))
    ((-6/5:ℝ)*(1*Real.exp ((-6/5:ℝ)*t))) t at h
  simpa only [one_mul] using h

theorem actual_negative_source_mode_decays_in_continuous_time :
    Tendsto (fun t : ℝ => Real.exp ((-6/5:ℝ)*t)) atTop (𝓝 0) := by
  have h := (actual_linear_all_initial_attraction_iff (-6/5)).mpr (by norm_num) 1
  change Tendsto (fun t : ℝ => 1*Real.exp ((-6/5:ℝ)*t)) atTop (𝓝 0) at h
  simpa only [one_mul] using h

theorem actual_positive_source_mode_grows_in_continuous_time :
    Tendsto (fun t : ℝ => Real.exp ((1/2:ℝ)*t)) atTop atTop := by
  have h := actual_positive_rate_grows (1/2) (by norm_num) 1 (by norm_num)
  change Tendsto (fun t : ℝ => 1*Real.exp ((1/2:ℝ)*t)) atTop atTop at h
  simpa only [one_mul] using h

theorem actual_same_source_scalar_modes_reverse_the_discrete_decay_test :
    Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => |(-6/5:ℝ)^n|) atTop atTop := by
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · simp_rw [abs_pow]
    norm_num
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

end SafeLearning.CompleteAppliedContinuousDiscreteContrast
