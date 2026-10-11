import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteFoundationsBalancedSensorReconstruction27
open CompleteFoundationsSpectralModels

def sensorH : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def inverseH : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,1/2;1/2,-1/2]
def sensorErrors : Set E := {eta | |eta 0| ≤ 1/10 ∧ |eta 1| ≤ 1/10}
def reconstructedErrors : Set E := applyMatrix inverseH '' sensorErrors

theorem actual_balanced_sensor_both_matrix_inverse_identities :
    inverseH * sensorH = 1 ∧ sensorH * inverseH = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sensorH,inverseH,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_balanced_sensor_actual_matrix_inverse : sensorH⁻¹ = inverseH := by
  exact Matrix.inv_eq_left_inv actual_balanced_sensor_both_matrix_inverse_identities.1

theorem actual_balanced_sensor_coordinate_action (x : E) :
    applyMatrix sensorH x = point (x 0+x 1) (x 0-x 1) := by
  rw [matrix_coordinate_action]
  simp [sensorH,sub_eq_add_neg]

theorem actual_balanced_inverse_coordinate_action (eta : E) :
    applyMatrix inverseH eta = point ((eta 0+eta 1)/2) ((eta 0-eta 1)/2) := by
  rw [matrix_coordinate_action]
  simp [inverseH,sub_eq_add_neg]
  congr 1 <;> ring

theorem actual_balanced_inverse_cancels_every_sensor_vector (x : E) :
    applyMatrix inverseH (applyMatrix sensorH x) = x := by
  rw [actual_balanced_inverse_coordinate_action,actual_balanced_sensor_coordinate_action]
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem actual_balanced_source_estimate_and_measurements :
    applyMatrix inverseH (point 6 2) = point 4 2 ∧
    applyMatrix sensorH (point 4 2) = point 6 2 := by
  rw [actual_balanced_inverse_coordinate_action,actual_balanced_sensor_coordinate_action]
  norm_num [point]

theorem actual_balanced_sensor_noisy_reconstruction_error (z eta : E) :
    applyMatrix (sensorH⁻¹) (applyMatrix sensorH z + eta)-z =
      applyMatrix inverseH eta := by
  rw [actual_balanced_sensor_actual_matrix_inverse,map_add,
    actual_balanced_inverse_cancels_every_sensor_vector,add_sub_cancel_left]

theorem actual_balanced_sensor_euclidean_squares (x : E) :
    ‖applyMatrix sensorH x‖^2 = 2*‖x‖^2 ∧
    ‖applyMatrix inverseH x‖^2 = ‖x‖^2/2 := by
  rw [actual_balanced_sensor_coordinate_action,actual_balanced_inverse_coordinate_action]
  simp only [norm_squared_coordinates,point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor <;> ring

theorem actual_balanced_reconstructed_error_exact_norm (eta : E) :
    ‖applyMatrix inverseH eta‖ = ‖eta‖/Real.sqrt 2 := by
  have hs := actual_balanced_sensor_euclidean_squares eta |>.2
  have hr : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he : (‖eta‖/Real.sqrt 2)^2=‖eta‖^2/2 := by
    rw [div_pow,hr]
  exact (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hp.le)).mp (hs.trans he.symm)

theorem actual_balanced_bounded_sensors_give_tenth_error (eta : E)
    (h : eta ∈ sensorErrors) : ‖applyMatrix inverseH eta‖ ≤ 1/10 := by
  have h0 := sq_le_sq₀ (abs_nonneg (eta 0)) (by norm_num : (0:ℝ)≤1/10) |>.mpr h.1
  have h1 := sq_le_sq₀ (abs_nonneg (eta 1)) (by norm_num : (0:ℝ)≤1/10) |>.mpr h.2
  have hs := actual_balanced_sensor_euclidean_squares eta |>.2
  rw [norm_squared_coordinates eta] at hs
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg (applyMatrix inverseH eta)]

theorem actual_balanced_error_set_is_the_rotated_square (e : E) :
    e∈reconstructedErrors ↔ |e 0+e 1|≤1/10 ∧ |e 0-e 1|≤1/10 := by
  constructor
  · rintro ⟨eta,h,rfl⟩
    rw [actual_balanced_inverse_coordinate_action]
    change |(eta 0+eta 1)/2+(eta 0-eta 1)/2|≤1/10 ∧
      |(eta 0+eta 1)/2-(eta 0-eta 1)/2|≤1/10
    have h0 : (eta 0+eta 1)/2+(eta 0-eta 1)/2=eta 0 := by ring
    have h1 : (eta 0+eta 1)/2-(eta 0-eta 1)/2=eta 1 := by ring
    simpa only [sensorErrors,Set.mem_setOf_eq,h0,h1] using h
  · intro h
    refine ⟨applyMatrix sensorH e,?_,actual_balanced_inverse_cancels_every_sensor_vector e⟩
    rw [actual_balanced_sensor_coordinate_action]
    exact h

theorem actual_balanced_error_coordinate_bound_and_forced_zero (e : E)
    (h : e∈reconstructedErrors) : |e 0|≤1/10 ∧
      (|e 0|=1/10 → e 1=0) := by
  have hr := actual_balanced_error_set_is_the_rotated_square e |>.mp h
  rcases abs_le.mp hr.1 with ⟨a,b⟩
  rcases abs_le.mp hr.2 with ⟨c,d⟩
  constructor
  · apply abs_le.mpr; constructor <;> linarith
  · intro he
    by_cases hp : 0 ≤ e 0
    · rw [abs_of_nonneg hp] at he; linarith
    · rw [abs_of_nonpos (le_of_not_ge hp)] at he; linarith

theorem actual_balanced_reconstructed_errors_have_sensor_corner_images :
    applyMatrix inverseH (point (1/10) (1/10)) = point (1/10) 0 ∧
    applyMatrix inverseH (point (-1/10) (-1/10)) = point (-1/10) 0 ∧
    applyMatrix inverseH (point (1/10) (-1/10)) = point 0 (1/10) ∧
    applyMatrix inverseH (point (-1/10) (1/10)) = point 0 (-1/10) := by
  simp only [actual_balanced_inverse_coordinate_action]
  norm_num [point]

theorem actual_balanced_reconstructed_errors_are_not_independent_coordinate_box :
    point (1/10) (1/10) ∉ reconstructedErrors := by
  rw [actual_balanced_error_set_is_the_rotated_square]
  norm_num [point]

theorem actual_balanced_true_displacement_maximum :
    IsGreatest {v : ℝ | ∃e∈reconstructedErrors,v=4-e 0} (41/10) := by
  constructor
  · refine ⟨point (-1/10) 0,?_,?_⟩
    · rw [actual_balanced_error_set_is_the_rotated_square]
      norm_num [point]
    · norm_num [point]
  · rintro v ⟨e,he,rfl⟩
    have h := actual_balanced_error_coordinate_bound_and_forced_zero e he |>.1
    have hl := abs_le.mp h |>.1
    linarith

theorem actual_balanced_fixture_upper_limit_decisions :
    (∀e∈reconstructedErrors,4-e 0≤83/20) ∧
      (∃e∈reconstructedErrors,81/20<4-e 0) := by
  constructor
  · intro e he
    have h := actual_balanced_true_displacement_maximum.2 ⟨e,he,rfl⟩
    linarith
  · obtain ⟨e,he,hv⟩ := actual_balanced_true_displacement_maximum.1
    exact ⟨e,he,by linarith⟩

end SafeLearning.CompleteFoundationsBalancedSensorReconstruction27
