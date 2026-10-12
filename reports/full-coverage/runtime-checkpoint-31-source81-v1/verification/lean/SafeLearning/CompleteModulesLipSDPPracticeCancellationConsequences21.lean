import SafeLearning.CompleteModulesLipSDPPracticeCancellation21

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix.Norms.L2Operator NNReal
namespace SafeLearning.CompleteModulesLipSDPPracticeCancellationConsequences21
open CompleteModulesLipSDPPracticeCancellation21

theorem actual_source_individual_spectral_norms :
    ‖firstWeight‖ = Real.sqrt 2 ∧ ‖absoluteLast‖ = Real.sqrt 2 := by
  have h := actual_cancellation_matrix_and_loop_bound
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · nlinarith [norm_nonneg firstWeight, Real.sqrt_nonneg 2]
  · nlinarith [norm_nonneg absoluteLast, Real.sqrt_nonneg 2]

theorem actual_source_half_sum_bound_is_one :
    (1 / 2 : ℝ) * ‖absoluteLast * firstWeight‖ +
      (1 / 2 : ℝ) * ‖absoluteLast‖ * ‖firstWeight‖ = 1 := by
  have h := actual_cancellation_matrix_and_loop_bound
  rw [h.1, norm_zero]
  nlinarith [h.2.2.2.1]

theorem actual_distinct_positive_pair_attains_gain_one :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ (1 : ℝ) ≠ 2 ∧
      |absoluteNetwork 2 - absoluteNetwork 1| = |(2 : ℝ) - 1| := by
  norm_num [actual_absolute_network_formula]

theorem actual_zero_bias_derivative_everywhere (x : ℝ) :
    HasDerivAt (biasedNetwork 0) 1 x := by
  have hf : biasedNetwork 0 = (fun t : ℝ => t) := by
    funext t
    exact (actual_identical_weights_zero_and_unit_bias_networks t).1
  rw [hf]
  exact hasDerivAt_id x

theorem actual_shifted_global_lipschitz_and_continuity :
    LipschitzWith 2 shifted ∧ Continuous shifted := by
  have hl : LipschitzWith 2 shifted := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      actual_shifted_least_gain_is_two.1.2 x y
  exact ⟨hl, hl.continuous⟩

theorem actual_shifted_piece_boundaries_agree :
    shifted (-1) = -2 ∧ shifted 1 = 2 ∧
      ContinuousAt shifted (-1) ∧ ContinuousAt shifted 1 := by
  refine ⟨?_, ?_, actual_shifted_global_lipschitz_and_continuity.2.continuousAt,
    actual_shifted_global_lipschitz_and_continuity.2.continuousAt⟩
  · norm_num [shifted]
  · norm_num [shifted]

end SafeLearning.CompleteModulesLipSDPPracticeCancellationConsequences21
