import SafeLearning.CompleteFiniteCMDPInverse
import SafeLearning.CompleteFiniteCMDPScaledSpectrum

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFiniteCMDPMatrixConsequences

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery SafeLearning.CompleteFiniteCMDPInverse
  SafeLearning.CompleteFiniteCMDPSpectrum SafeLearning.CompleteFiniteCMDPScaledSpectrum

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

theorem actual_model_state_type_nonempty (M : Model S A) : Nonempty S := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    letI := h
    have hp := M.initial_sum
    simp at hp
  | inr h => exact h

theorem actual_recovered_policy_kernel_standard_spectral_radius_one
    (M : Model S A) (a₀ : A) (ρ : S → A → ℝ) (hρ : ∀ s a, 0 ≤ ρ s a) :
    spectralRadius ℂ (complexMatrix (stationaryKernel M (recoveredAction a₀ ρ))) = 1 := by
  letI := actual_model_state_type_nonempty M
  have hK := actual_stationary_kernel_probability_law M (recoveredAction a₀ ρ)
    (actual_recovered_action_nonneg a₀ ρ hρ)
    (actual_recovered_action_normalized a₀ ρ hρ)
  exact actual_stochastic_matrix_standard_spectral_radius_one _ hK.1 hK.2

theorem actual_recovered_policy_discounted_complex_kernel_is_unit
    (M : Model S A) (a₀ : A) (ρ : S → A → ℝ) (hρ : ∀ s a, 0 ≤ ρ s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit ((1 : Matrix S S ℂ) - (γ : ℂ) •
      complexMatrix (stationaryKernel M (recoveredAction a₀ ρ))) := by
  have hK := actual_stationary_kernel_probability_law M (recoveredAction a₀ ρ)
    (actual_recovered_action_nonneg a₀ ρ hρ)
    (actual_recovered_action_normalized a₀ ρ hρ)
  exact actual_complex_discounted_stochastic_matrix_is_unit _ hK.1 hK.2 γ hγ0 hγ1

theorem actual_recovered_flow_has_source_row_equation_and_inverse_formula
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ) :
    stateMarginal ρ ᵥ* discountedMatrix (stationaryKernel M (recoveredAction a₀ ρ)) γ =
        (1 - γ) • M.initial ∧
      stateMarginal ρ = ((1 - γ) • M.initial) ᵥ*
        (discountedMatrix (stationaryKernel M (recoveredAction a₀ ρ)) γ)⁻¹ := by
  constructor
  · have hx := actual_flow_factorization_gives_kernel_fixed_point M γ ρ
      (recoveredAction a₀ ρ) hρ (actual_recovered_row_action_product a₀ ρ hρ.1)
    let K : Matrix S S ℝ := stationaryKernel M (recoveredAction a₀ ρ)
    change ∀ t, stateMarginal ρ t = (1 - γ) * M.initial t +
      γ * ∑ s, stateMarginal ρ s * K s t at hx
    have hscale : stateMarginal ρ ᵥ* (γ • K) = γ • (stateMarginal ρ ᵥ* K) :=
      Matrix.vecMul_smul _ γ K
    change stateMarginal ρ ᵥ* (1 - γ • K) =
      (1 - γ) • M.initial
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, hscale]
    ext t
    change stateMarginal ρ t - γ *
      (∑ s, stateMarginal ρ s * K s t) =
      (1 - γ) * M.initial t
    linarith [hx t]
  · exact actual_recovered_flow_state_marginal_inverse_formula M a₀ γ hγ0 hγ1 ρ hρ

end SafeLearning.CompleteFiniteCMDPMatrixConsequences
