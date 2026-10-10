import SafeLearning.CompleteModulesEllipsoidExample

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped Matrix
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidOptimum
open SafeLearning.CompleteModulesEllipsoidExample
namespace SafeLearning.CompleteModulesEllipsoidCorollaries

theorem actual_source_normalized_matrix_is_positive_semidefinite : actualNormalized.PosSemidef := by
  have hh : actualNormalized.IsHermitian := by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [actualNormalized]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro vector
  simp [actualNormalized,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  nlinarith [sq_nonneg (vector 0+vector 1/2)]

theorem actual_source_true_largest_normalized_eigenvalue_is_five_fourths :
    actualMaximumEigenvalue (actualNormalizedQuadratic actualStorage actualObjective)
      (actual_normalized_quadratic_is_symmetric actualStorage actualObjective
        actual_source_storage_is_positive_definite actual_source_objective_is_symmetric)=5/4 := by
  let hm := actual_normalized_quadratic_is_symmetric actualStorage actualObjective
    actual_source_storage_is_positive_definite actual_source_objective_is_symmetric
  have hg := actual_ellipsoid_quadratic_maximum actualStorage actualObjective
    actual_source_storage_is_positive_definite actual_source_objective_is_symmetric
  have hn := actual_source_ellipsoid_maximum_is_five_fourths
  have he : max 0 (actualMaximumEigenvalue _ hm)=(5/4:ℝ) := hg.unique hn
  obtain ⟨index,hi⟩ := actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues _ hm
  have hp : (actualNormalizedQuadratic actualStorage actualObjective).PosSemidef := by
    rw [actual_source_normalized_matrix]
    exact actual_source_normalized_matrix_is_positive_semidefinite
  have hnon : 0 ≤ actualMaximumEigenvalue _ hm := by
    rw [hi]
    exact (hm.posSemidef_iff_eigenvalues_nonneg.mp hp) index
  rwa [max_eq_right hnon] at he

theorem actual_source_smallest_certificate_multiplier_is_five_fourths :
    IsLeast (actualMultipliers actualStorage actualObjective) (5/4) := by
  have h := actual_smallest_nonnegative_s_procedure_multiplier actualStorage actualObjective
    actual_source_storage_is_positive_definite actual_source_objective_is_symmetric
  rwa [actual_source_true_largest_normalized_eigenvalue_is_five_fourths,max_eq_right (by norm_num : (0:ℝ)≤5/4)] at h

theorem actual_source_certificate_and_maximizer_complementary_slackness :
    ((5/4:ℝ) • actualStorage-actualObjective)*ᵥ actualMaximizer=0 ∧
      (5/4:ℝ)*(quadraticValue actualStorage actualMaximizer-1)=0 := by
  constructor
  · ext index
    fin_cases index <;>
      simp [actualStorage,actualObjective,actualMaximizer,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring
  · rw [actual_source_maximizer_has_energy_one_and_objective_five_fourths.1]
    ring

end SafeLearning.CompleteModulesEllipsoidCorollaries
