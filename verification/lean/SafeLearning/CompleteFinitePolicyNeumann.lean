import SafeLearning.CompleteFiniteCMDPInverse

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator NNReal

namespace SafeLearning.CompleteFinitePolicyNeumann

open SafeLearning.CompleteFiniteCMDPInverse

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

-- Use the topology supplied by the stated operator norm for the matrix series.
local instance : MetricSpace (Matrix S S ℝ) :=
  @NormedRing.toMetricSpace (Matrix S S ℝ) Matrix.linftyOpNormedRing
local instance : UniformSpace (Matrix S S ℝ) := PseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace (Matrix S S ℝ) := UniformSpace.toTopologicalSpace

theorem actual_row_stochastic_operator_norm
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t)
    (hK1 : ∀ s, ∑ t, K s t = 1) : ‖K‖ = 1 := by
  have row : ∀ s, (∑ t, ‖K s t‖₊ : ℝ≥0) = 1 := by
    intro s
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hK0 s _)]
    exact hK1 s
  rw [Matrix.linfty_opNorm_def]
  simp_rw [row]
  simp [Finset.sup_const Finset.univ_nonempty]

theorem actual_discounted_operator_norm
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t)
    (hK1 : ∀ s, ∑ t, K s t = 1) (γ : ℝ) (hγ0 : 0 ≤ γ) :
    ‖γ • K‖ = γ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0,
    actual_row_stochastic_operator_norm K hK0 hK1, mul_one]

theorem actual_matrix_geometric_series_summable
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t)
    (hK1 : ∀ s, ∑ t, K s t = 1) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Summable (fun n : ℕ => γ ^ n • K ^ n) := by
  have hn : ‖γ • K‖ < 1 := by
    rw [actual_discounted_operator_norm K hK0 hK1 γ hγ0]
    exact hγ1
  simpa only [smul_pow] using summable_geometric_of_norm_lt_one hn

theorem actual_literal_neumann_inverse
    (K : Matrix S S ℝ) (hK0 : ∀ s t, 0 ≤ K s t)
    (hK1 : ∀ s, ∑ t, K s t = 1) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (discountedMatrix K γ)⁻¹ = ∑' n : ℕ, γ ^ n • K ^ n := by
  have hn : ‖γ • K‖ < 1 := by
    rw [actual_discounted_operator_norm K hK0 hK1 γ hγ0]
    exact hγ1
  rw [discountedMatrix, Matrix.nonsing_inv_eq_ringInverse]
  simpa only [smul_pow] using (geom_series_eq_inverse (γ • K) hn).symm

end SafeLearning.CompleteFinitePolicyNeumann
