import SafeLearning.CompleteModulesScalarBoundedReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesScalarGainCorollaries
open CompleteModulesScalarBoundedReal

theorem actual_scalar_source_certificate_eigenvalues (eigenvalue : ℝ) :
    eigenvalue ∈ spectrum ℝ (actualScalarGainMatrix 2 2) ↔
      eigenvalue=0 ∨ eigenvalue= -(5/2:ℝ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,
    actual_scalar_source_matrix_trace_determinant_characteristic_polynomial.2.2]
  simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_C,mul_eq_zero]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem actual_scalar_nonnegative_gain_is_certifiable_iff_at_least_two (gain : ℝ) (hgain : 0 ≤ gain) :
    (∃ storage : ℝ,0 ≤ storage ∧ (-actualScalarGainMatrix storage gain).PosSemidef) ↔ 2 ≤ gain := by
  constructor
  · rintro ⟨storage,hstorage,hcertificate⟩
    exact actual_scalar_certificate_requires_gain_at_least_two storage gain hgain hcertificate
  · intro htwo
    refine ⟨2,by norm_num,?_⟩
    rw [actual_scalar_schur_required_gain_formula 2 gain (by norm_num)]
    norm_num [actualScalarRequiredGainSquared]
    nlinarith

end SafeLearning.CompleteModulesScalarGainCorollaries
