import SafeLearning.CompletePolicyQuadraticDual

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyFeasibleTRPO
open SafeLearning.CompletePolicyQuadraticDual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def q (H : Matrix ι ι ℝ) (g : ι → ℝ) : ℝ := g ⬝ᵥ (H⁻¹ *ᵥ g)
def r (H : Matrix ι ι ℝ) (g b : ι → ℝ) : ℝ := g ⬝ᵥ (H⁻¹ *ᵥ b)
def lambdaZero (H : Matrix ι ι ℝ) (g : ι → ℝ) (δ : ℝ) : ℝ :=
  Real.sqrt (q H g / (2 * δ))
def trpo (H : Matrix ι ι ℝ) (g b : ι → ℝ) (δ : ℝ) : ι → ℝ :=
  optimizer H g b (lambdaZero H g δ) 0

theorem actual_q_positive (H : Matrix ι ι ℝ) (hH : H.PosDef) (g : ι → ℝ) (hg : g ≠ 0) :
    0 < q H g := by
  simpa [q] using hH.inv.dotProduct_mulVec_pos hg

theorem actual_lambda_zero_positive_and_square (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g : ι → ℝ) (hg : g ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    0 < lambdaZero H g δ ∧ (lambdaZero H g δ) ^ 2 = q H g / (2 * δ) := by
  have hp : 0 < q H g / (2 * δ) := div_pos (actual_q_positive H hH g hg) (by positivity)
  exact ⟨Real.sqrt_pos.mpr hp,Real.sq_sqrt hp.le⟩

theorem actual_lambda_reciprocal_is_printed_trpo_scale (H : Matrix ι ι ℝ)
    (g : ι → ℝ) (δ : ℝ) :
    1 / lambdaZero H g δ = Real.sqrt (2 * δ / q H g) := by
  rw [lambdaZero, one_div, ← Real.sqrt_inv, inv_div]

theorem actual_trpo_is_literal_inverse_gradient_step (H : Matrix ι ι ℝ)
    (g b : ι → ℝ) (δ : ℝ) :
    trpo H g b δ = Real.sqrt (2 * δ / q H g) • (H⁻¹ *ᵥ g) := by
  simp only [trpo, optimizer, zero_smul, sub_zero]
  rw [actual_lambda_reciprocal_is_printed_trpo_scale]

theorem actual_trpo_saturates_the_actual_metric_region (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (hg : g ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    (trpo H g b δ ⬝ᵥ (H *ᵥ trpo H g b δ)) / 2 = δ := by
  obtain ⟨hp,hs⟩ := actual_lambda_zero_positive_and_square H hH g hg δ hδ
  have he : q H g = 2 * δ * (lambdaZero H g δ) ^ 2 := by
    have := (eq_div_iff (by positivity : (2 : ℝ) * δ ≠ 0)).mp hs
    nlinarith
  simp only [trpo, optimizer, zero_smul, sub_zero, mulVec_smul, actual_inverse_solves H hH,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (H⁻¹ *ᵥ g) g, ← q, he]
  field_simp [ne_of_gt hp]
  <;> ring

theorem actual_printed_scalar_test_is_true_linearized_feasibility
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (c δ : ℝ) :
    c + b ⬝ᵥ trpo H g b δ = c + r H g b * Real.sqrt (2 * δ / q H g) := by
  rw [actual_trpo_is_literal_inverse_gradient_step, dotProduct_smul]
  have hc := actual_real_symmetric_form H⁻¹ hH.inv b g
  simpa [r, smul_eq_mul, mul_comm] using congrArg
    (fun t : ℝ => c + Real.sqrt (2 * δ / q H g) * t) hc

theorem actual_trpo_reward_equals_its_true_dual_value
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ) :
    actualDual H g b c δ (lambdaZero H g δ,0) = g ⬝ᵥ trpo H g b δ := by
  have hp := (actual_lambda_zero_positive_and_square H hH g hg δ hδ).1
  rw [actual_true_supremum_equals_closed_dual H hH g b c δ (lambdaZero H g δ) 0 hp,
    ← actual_attained_closed_dual_value H hH g b c δ (lambdaZero H g δ) 0 hp]
  change lagrangian H g b c δ (lambdaZero H g δ) 0 (trpo H g b δ) = _
  rw [lagrangian, actual_trpo_saturates_the_actual_metric_region H hH g b hg δ hδ]
  ring

theorem actual_feasible_trpo_is_a_global_joint_dual_minimum
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ)
    (hfeasible : c + r H g b * Real.sqrt (2 * δ / q H g) ≤ 0)
    (lam ν : ℝ) (hlam : 0 < lam) (hν : 0 ≤ ν) :
    actualDual H g b c δ (lambdaZero H g δ,0) ≤ actualDual H g b c δ (lam,ν) := by
  rw [actual_trpo_reward_equals_its_true_dual_value H hH g b hg c δ hδ]
  exact actual_weak_duality H hH g b c δ lam ν hlam hν (trpo H g b δ)
    (by rwa [actual_printed_scalar_test_is_true_linearized_feasibility H hH g b c δ])
    (le_of_eq (actual_trpo_saturates_the_actual_metric_region H hH g b hg δ hδ))

theorem actual_trpo_bounds_every_feasible_reward
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ) (x : ι → ℝ)
    (hcost : c + b ⬝ᵥ x ≤ 0) (htrust : (x ⬝ᵥ (H *ᵥ x)) / 2 ≤ δ) :
    g ⬝ᵥ x ≤ g ⬝ᵥ trpo H g b δ := by
  rw [← actual_trpo_reward_equals_its_true_dual_value H hH g b hg c δ hδ]
  exact actual_weak_duality H hH g b c δ (lambdaZero H g δ) 0
    (actual_lambda_zero_positive_and_square H hH g hg δ hδ).1 (by norm_num) x hcost htrust

end SafeLearning.CompletePolicyFeasibleTRPO
