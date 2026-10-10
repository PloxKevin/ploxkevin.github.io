import SafeLearning.CompleteModulesScalarBoundedReal
import SafeLearning.CompleteModulesTwoByTwoNSD

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesScalarGainDetails
open CompleteModulesScalarBoundedReal CompleteModulesTwoByTwoNSD

theorem actual_source_scalar_gain_matrix_exact_entries :
    actualScalarGainMatrix 2 2=!![-(1/2:ℝ),1;1,-2] := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [actualScalarGainMatrix]

theorem actual_boundary_storage_matrix_entries_and_negative_determinant (gain : ℝ) :
    actualScalarGainMatrix (4/3) gain 0 0=0 ∧
    actualScalarGainMatrix (4/3) gain 0 1=(2/3:ℝ) ∧
    (actualScalarGainMatrix (4/3) gain).det= -(4/9:ℝ) := by
  norm_num [actualScalarGainMatrix,Matrix.det_fin_two]

theorem actual_scalar_gain_matrix_negative_semidefinite_iff_diagonals_and_determinant (storage gain : ℝ) :
    (-actualScalarGainMatrix storage gain).PosSemidef ↔
    1-3*storage/4 ≤ 0 ∧ storage-gain^2 ≤ 0 ∧ 0 ≤ (actualScalarGainMatrix storage gain).det := by
  rw [actualScalarGainMatrix,actual_symmetric_two_by_two_negative_matrix_criterion]
  simp [Matrix.det_fin_two,pow_two]

theorem actual_source_scalar_schur_alternative_required_gain_expression (storage : ℝ)
    (hstorage : (4/3:ℝ) < storage) :
    storage+(1/4:ℝ)*storage^2/((3/4:ℝ)*storage-1)=actualScalarRequiredGainSquared storage := by
  have hden : 3*storage-4≠0 := by linarith
  unfold actualScalarRequiredGainSquared
  rw [show (3/4:ℝ)*storage-1=(3*storage-4)/4 by ring]
  field_simp [hden]

theorem actual_scalar_source_critical_equation_roots (storage : ℝ) :
    (3*storage^2-8*storage+4=0) ↔ storage=2 ∨ storage=(2/3:ℝ) := by
  rw [show 3*storage^2-8*storage+4=(3*storage-2)*(storage-2) by ring,mul_eq_zero]
  constructor
  · rintro (h|h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h|h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

theorem actual_scalar_source_other_critical_root_is_outside_storage_domain :
    ¬ ((4/3:ℝ) < 2/3) := by norm_num

end SafeLearning.CompleteModulesScalarGainDetails
