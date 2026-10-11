import SafeLearning.CompleteFiniteCMDPRecovery

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFiniteCMDPInverse

open SafeLearning.CompleteFiniteCMDPOccupancy SafeLearning.CompleteFiniteCMDPFlow
  SafeLearning.CompleteFiniteCMDPRecovery

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

def discountedMatrix (K : Matrix S S ℝ) (γ : ℝ) : Matrix S S ℝ := 1 - γ • K

theorem actual_discounted_stochastic_matrix_is_unit
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : IsUnit (discountedMatrix K γ) := by
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro x y hxy
  have hu : ∀ t, (x - y) t = γ * ∑ s, (x - y) s * K s t := by
    intro t
    have he := congrArg (fun z : S → ℝ => z t) hxy
    simp only [discountedMatrix, Matrix.vecMul_sub, Matrix.vecMul_one,
      Matrix.vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at he
    change x t - γ * (∑ s, x s * K s t) = y t - γ * (∑ s, y s * K s t) at he
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    linarith
  have hz : x - y = (0 : S → ℝ) :=
    actual_stochastic_discounted_fixed_point_unique K hK0 hK1 γ hγ0 hγ1
      0 (x - y) 0
      (fun t => by simpa using hu t)
      (fun t => by simp)
  exact sub_eq_zero.mp hz

theorem actual_discounted_stochastic_matrix_two_sided_inverse
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    discountedMatrix K γ * (discountedMatrix K γ)⁻¹ = 1 ∧
      (discountedMatrix K γ)⁻¹ * discountedMatrix K γ = 1 := by
  have hd : IsUnit (discountedMatrix K γ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (actual_discounted_stochastic_matrix_is_unit K hK0 hK1 γ hγ0 hγ1)
  exact ⟨Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩

theorem actual_stochastic_fixed_point_has_literal_inverse_formula
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t) (hK1 : ∀ s, ∑ t, K s t = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ x : S → ℝ)
    (hx : ∀ t, x t = (1 - γ) * μ t + γ * ∑ s, x s * K s t) :
    x = ((1 - γ) • μ) ᵥ* (discountedMatrix K γ)⁻¹ := by
  have he : x ᵥ* discountedMatrix K γ = (1 - γ) • μ := by
    ext t
    simp only [discountedMatrix, Matrix.vecMul_sub, Matrix.vecMul_one,
      Matrix.vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change x t - γ * (∑ s, x s * K s t) = (1 - γ) * μ t
    linarith [hx t]
  have hi := (actual_discounted_stochastic_matrix_two_sided_inverse K hK0 hK1 γ hγ0 hγ1).1
  calc
    x = x ᵥ* (discountedMatrix K γ * (discountedMatrix K γ)⁻¹) := by rw [hi, Matrix.vecMul_one]
    _ = (x ᵥ* discountedMatrix K γ) ᵥ* (discountedMatrix K γ)⁻¹ :=
      (Matrix.vecMul_vecMul _ _ _).symm
    _ = _ := congrArg (fun z : S → ℝ => z ᵥ* (discountedMatrix K γ)⁻¹) he

theorem actual_recovered_flow_state_marginal_inverse_formula
    (M : Model S A) (a₀ : A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → A → ℝ) (hρ : FlowFeasible M γ ρ) :
    stateMarginal ρ = ((1 - γ) • M.initial) ᵥ*
      (discountedMatrix (stationaryKernel M (recoveredAction a₀ ρ)) γ)⁻¹ := by
  have hK := actual_stationary_kernel_probability_law M (recoveredAction a₀ ρ)
    (actual_recovered_action_nonneg a₀ ρ hρ.1)
    (actual_recovered_action_normalized a₀ ρ hρ.1)
  exact actual_stochastic_fixed_point_has_literal_inverse_formula _ hK.1 hK.2 γ hγ0 hγ1
    M.initial (stateMarginal ρ)
    (actual_flow_factorization_gives_kernel_fixed_point M γ ρ (recoveredAction a₀ ρ) hρ
      (actual_recovered_row_action_product a₀ ρ hρ.1))

end SafeLearning.CompleteFiniteCMDPInverse
