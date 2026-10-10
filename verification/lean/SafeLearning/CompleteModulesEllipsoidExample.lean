import SafeLearning.CompleteModulesEllipsoidOptimum

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped Matrix MatrixOrder
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidRoot
open SafeLearning.CompleteModulesEllipsoidOptimum
namespace SafeLearning.CompleteModulesEllipsoidExample

def actualStorage : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,4]
def actualObjective : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,1]
def actualInverseRoot : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,1/2]
def actualNormalized : Matrix (Fin 2) (Fin 2) ℝ := !![1,1/2;1/2,1/4]

theorem actual_source_storage_is_positive_definite : actualStorage.PosDef := by
  rw [actualStorage,Matrix.posDef_diagonal_iff]
  intro index
  fin_cases index <;> norm_num

theorem actual_source_objective_is_symmetric : actualObjective.IsHermitian := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [actualObjective]

theorem actual_source_storage_inverse : actualStorage⁻¹=Matrix.diagonal ![1,1/4] := by
  apply Matrix.inv_eq_right_inv
  rw [actualStorage,Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [Matrix.one_apply]

theorem actual_source_inverse_positive_square_root :
    actualInversePositiveSquareRoot actualStorage=actualInverseRoot := by
  unfold actualInversePositiveSquareRoot
  rw [actual_source_storage_inverse]
  apply CFC.sqrt_unique
  · rw [actualInverseRoot,Matrix.diagonal_mul_diagonal]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num
  · apply Matrix.PosSemidef.nonneg
    rw [actualInverseRoot,Matrix.posSemidef_diagonal_iff]
    intro index
    fin_cases index <;> norm_num

theorem actual_source_normalized_matrix :
    actualNormalizedQuadratic actualStorage actualObjective=actualNormalized := by
  rw [actualNormalizedQuadratic,actual_source_inverse_positive_square_root]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [actualInverseRoot,actualObjective,actualNormalized,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_source_normalized_trace_and_determinant :
    actualNormalized.trace=5/4 ∧ actualNormalized.det=0 := by
  constructor <;> norm_num [actualNormalized,Matrix.trace,Fin.sum_univ_two,Matrix.det_fin_two]

theorem actual_source_normalized_complete_characteristic_roots (value : ℂ) :
    Matrix.det (value • (1 : Matrix (Fin 2) (Fin 2) ℂ)-actualNormalized.map (algebraMap ℝ ℂ))=0 ↔
      value=0 ∨ value=5/4 := by
  have he : Matrix.det (value • (1 : Matrix (Fin 2) (Fin 2) ℂ)-actualNormalized.map (algebraMap ℝ ℂ))=
      value*(value-5/4) := by
    norm_num [actualNormalized,Matrix.det_fin_two]
    ring
  rw [he,mul_eq_zero,sub_eq_zero]

theorem actual_source_storage_and_objective_quadratic_identities (vector : Fin 2 → ℝ) :
    quadraticValue actualStorage vector=(vector 0)^2+4*(vector 1)^2 ∧
      quadraticValue actualObjective vector=(vector 0+vector 1)^2 := by
  constructor <;> simp [quadraticValue,actualStorage,actualObjective,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring

theorem actual_source_cauchy_schwarz_upper_bound (vector : Fin 2 → ℝ) :
    (vector 0+vector 1)^2 ≤ ((vector 0)^2+4*(vector 1)^2)*(1+(1/4:ℝ)) := by
  nlinarith [sq_nonneg (vector 0/2-2*vector 1)]

def actualMaximizer : Fin 2 → ℝ := ![2/Real.sqrt 5,1/(2*Real.sqrt 5)]

theorem actual_source_maximizer_has_energy_one_and_objective_five_fourths :
    quadraticValue actualStorage actualMaximizer=1 ∧
      quadraticValue actualObjective actualMaximizer=5/4 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hn : Real.sqrt (5:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [(actual_source_storage_and_objective_quadratic_identities actualMaximizer).1,
    (actual_source_storage_and_objective_quadratic_identities actualMaximizer).2]
  norm_num [actualMaximizer]
  constructor <;> field_simp <;> nlinarith

theorem actual_source_ellipsoid_maximum_is_five_fourths :
    IsGreatest (ellipsoidValues actualStorage actualObjective) (5/4) := by
  obtain ⟨he,hv⟩ := actual_source_maximizer_has_energy_one_and_objective_five_fourths
  constructor
  · exact ⟨actualMaximizer,he.le,hv.symm⟩
  · rintro value ⟨vector,henergy,rfl⟩
    obtain ⟨henergyid,hobjectiveid⟩ := actual_source_storage_and_objective_quadratic_identities vector
    rw [hobjectiveid]
    have hc := actual_source_cauchy_schwarz_upper_bound vector
    rw [henergyid] at henergy
    nlinarith

theorem actual_source_maximizer_is_in_the_printed_equality_direction :
    actualMaximizer=(2/Real.sqrt 5) • (![1,1/4] : Fin 2 → ℝ) := by
  ext index
  fin_cases index <;> norm_num [actualMaximizer] <;> ring

end SafeLearning.CompleteModulesEllipsoidExample
