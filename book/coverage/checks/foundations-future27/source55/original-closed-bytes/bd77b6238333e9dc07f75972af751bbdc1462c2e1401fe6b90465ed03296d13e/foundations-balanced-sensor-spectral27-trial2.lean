import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteFoundationsBalancedSensorSpectral27
open CompleteFoundationsSpectralModels

def sensorH : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def sensorLin : E →ₗ[ℝ] E := sensorH.toEuclideanLin
def spectralConditionNumber : ℝ := sensorLin.singularValues 0 / sensorLin.singularValues 1

theorem actual_balanced_sensor_matrix_action (x : E) :
    applyMatrix sensorH x = point (x 0+x 1) (x 0-x 1) := by
  rw [matrix_coordinate_action]
  simp [sensorH,sub_eq_add_neg]

theorem actual_balanced_sensor_source_measurements :
    applyMatrix sensorH (point 4 2) = point 6 2 := by
  rw [actual_balanced_sensor_matrix_action]
  norm_num [point]

theorem actual_balanced_sensor_transpose_gram :
    sensorH.transpose * sensorH = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sensorH,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_balanced_sensor_quadratic_identity (x : E) :
    inner ℝ x (applyMatrix (sensorH.transpose * sensorH) x) = 2*‖x‖^2 := by
  rw [actual_balanced_sensor_transpose_gram,matrix_coordinate_action,inner_coordinate_formula,
    norm_squared_coordinates]
  simp [point]
  ring

theorem actual_balanced_sensor_exact_squared_stretch (x : E) :
    ‖applyMatrix sensorH x‖^2 = 2*‖x‖^2 := by
  rw [actual_balanced_sensor_matrix_action]
  simp only [norm_squared_coordinates,point,PiLp.toLp_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem actual_balanced_sensor_exact_norm_stretch (x : E) :
    ‖applyMatrix sensorH x‖ = Real.sqrt 2*‖x‖ := by
  have hs := actual_balanced_sensor_exact_squared_stretch x
  have hr : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,hr]
  exact hs

theorem actual_balanced_sensor_adjoint_gram :
    sensorLin.adjoint.comp sensorLin = (2 : ℝ) • LinearMap.id := by
  have ht : sensorH.conjTranspose = sensorH := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sensorH,Matrix.conjTranspose_apply]
  unfold sensorLin
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,ht]
  ext x i
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply]
  change (applyMatrix sensorH (applyMatrix sensorH x)) i = (2 • x) i
  rw [actual_balanced_sensor_matrix_action,actual_balanced_sensor_matrix_action]
  fin_cases i <;> simp [point] <;> ring

theorem actual_balanced_sensor_all_genuine_singular_values (i : ℕ) :
    sensorLin.singularValues i = if i < 2 then Real.sqrt 2 else 0 := by
  have hd : Module.finrank ℝ E = 2 := by
    simp [E]
  by_cases hi : i < 2
  · rw [if_pos hi]
    have hEig := sensorLin.hasEigenvalue_adjoint_comp_self_sq_singularValues (by simpa [hd] using hi)
    obtain ⟨x,hx⟩ := hEig.exists_hasEigenvector
    have hne : x ≠ 0 := (Module.End.hasEigenvector_iff.mp hx).2
    have he := hx.apply_eq_smul
    rw [actual_balanced_sensor_adjoint_gram] at he
    simp only [LinearMap.smul_apply,LinearMap.id_apply] at he
    have hz : (2 - sensorLin.singularValues i ^ 2) • x = 0 := by
      change 2 • x = sensorLin.singularValues i ^ 2 • x at he
      rw [sub_smul,he,sub_self]
    have hsq : sensorLin.singularValues i ^ 2 = 2 := by
      have hh := (smul_eq_zero.mp hz).resolve_right hne
      linarith
    exact (sq_eq_sq₀ (sensorLin.singularValues_nonneg i) (Real.sqrt_nonneg 2)).mp
      (hsq.trans (Real.sq_sqrt (by norm_num)).symm)
  · rw [if_neg hi]
    exact sensorLin.singularValues_of_finrank_le (by simpa [hd] using Nat.le_of_not_gt hi)

theorem actual_balanced_sensor_both_singular_values_and_condition_number :
    sensorLin.singularValues 0 = Real.sqrt 2 ∧
    sensorLin.singularValues 1 = Real.sqrt 2 ∧ spectralConditionNumber = 1 := by
  have h0 := actual_balanced_sensor_all_genuine_singular_values 0
  have h1 := actual_balanced_sensor_all_genuine_singular_values 1
  norm_num at h0 h1
  refine ⟨h0,h1,?_⟩
  rw [spectralConditionNumber,h0,h1]
  exact div_self (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

theorem actual_balanced_sensor_every_unit_direction_has_the_same_stretch
    (x y : E) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖applyMatrix sensorH x‖ = Real.sqrt 2 ∧
    ‖applyMatrix sensorH y‖ = Real.sqrt 2 ∧
    ‖applyMatrix sensorH x‖ = ‖applyMatrix sensorH y‖ := by
  simp [actual_balanced_sensor_exact_norm_stretch,hx,hy]

end SafeLearning.CompleteFoundationsBalancedSensorSpectral27
