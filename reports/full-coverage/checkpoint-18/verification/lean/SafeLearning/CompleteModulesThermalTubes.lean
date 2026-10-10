import SafeLearning.CompleteModulesDynamics
import SafeLearning.CompleteModulesTheory
import SafeLearning.CompleteModulesBook

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set Filter
namespace SafeLearning.CompleteModulesThermalTubes
open CompleteModulesDynamics

abbrev E := EuclideanSpace ℝ (Fin 2)
def actualThermalMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![3/5,1/10;1/10,7/10]
def actualThermalOperator : E→L[ℝ] E := Matrix.toEuclideanCLM (n:=Fin 2) (𝕜:=ℝ) actualThermalMatrix

theorem actual_thermal_operator_coordinates (x : E) :
    actualThermalOperator x 0=thermalFirst (x 0) (x 1) ∧
    actualThermalOperator x 1=thermalSecond (x 0) (x 1) := by
  change (actualThermalMatrix*ᵥ (x : Fin 2→ℝ)) 0=thermalFirst (x 0) (x 1) ∧
    (actualThermalMatrix*ᵥ (x : Fin 2→ℝ)) 1=thermalSecond (x 0) (x 1)
  constructor <;> simp [actualThermalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    thermalFirst,thermalSecond]

theorem actual_thermal_euclidean_norm_is_the_literal_square_root (x : E) :
    ‖x‖=l2 (x 0) (x 1) := by
  simp [EuclideanSpace.norm_eq,l2,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]

theorem actual_thermal_euclidean_norm_squared (x : E) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  rw [actual_thermal_euclidean_norm_is_the_literal_square_root,l2]
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem actual_coordinate_magnitude_at_most_euclidean_norm (x : E) (index : Fin 2) :
    |x index|≤‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x index

theorem actual_thermal_operator_norm_bound (x : E) :
    ‖actualThermalOperator x‖≤thermalGain*‖x‖ := by
  rw [actual_thermal_euclidean_norm_is_the_literal_square_root,
    actual_thermal_operator_coordinates x |>.1,actual_thermal_operator_coordinates x |>.2,
    actual_thermal_euclidean_norm_is_the_literal_square_root]
  exact thermal_l2_gain _ _

theorem actual_startup_box_has_the_literal_energy_and_radius_bound
    (x : E) (hx : ∀ index,|x index|≤7/10) :
    ‖x‖^2≤49/50 ∧ ‖x‖≤Real.sqrt (49/50) ∧ ‖x‖≤1 ∧
    (∀ index,|x index|≤Real.sqrt (49/50)) ∧
    (∀ index,|actualThermalOperator x index|≤thermalGain*Real.sqrt (49/50)) := by
  have he:=CompleteModulesBook.startup_box_energy (x 0) (x 1) (hx 0) (hx 1)
  rw [←actual_thermal_euclidean_norm_squared] at he
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤49/50)
  have hr : ‖x‖≤Real.sqrt (49/50) := by nlinarith [norm_nonneg x,Real.sqrt_nonneg (49/50)]
  refine ⟨he,hr,by nlinarith [norm_nonneg x],?_,?_⟩
  · intro index
    exact (actual_coordinate_magnitude_at_most_euclidean_norm x index).trans hr
  · intro index
    exact (actual_coordinate_magnitude_at_most_euclidean_norm _ index).trans
      ((actual_thermal_operator_norm_bound x).trans
        (mul_le_mul_of_nonneg_left hr thermal_gain_positive_lt_one.1.le))

theorem actual_thermal_disturbed_step_bound (x w : E) :
    ‖actualThermalOperator x+w‖≤thermalGain*‖x‖+‖w‖ :=
  (norm_add_le _ _).trans (add_le_add (actual_thermal_operator_norm_bound x) le_rfl)

def actualTubeRadius : ℝ := (1/20)/(1-thermalGain)

theorem actual_source_tube_radius_is_positive_and_solves_the_fixed_radius_equation :
    0<actualTubeRadius ∧ thermalGain*actualTubeRadius+1/20=actualTubeRadius := by
  have hd : 0<1-thermalGain := by linarith [thermal_gain_positive_lt_one.2]
  refine ⟨div_pos (by norm_num) hd,?_⟩
  unfold actualTubeRadius
  field_simp
  ring

theorem actual_invariant_radius_scalar_condition_iff_the_source_tube_radius (radius : ℝ) :
    thermalGain*radius+1/20≤radius ↔ actualTubeRadius≤radius := by
  unfold actualTubeRadius
  rw [div_le_iff₀ (by linarith [thermal_gain_positive_lt_one.2])]
  constructor <;> intro h <;> linarith

theorem actual_tube_radius_invariant_step (x w : E) (radius : ℝ)
    (hx : ‖x‖≤radius) (hw : ‖w‖≤1/20) (hr : actualTubeRadius≤radius) :
    ‖actualThermalOperator x+w‖≤radius := by
  have hs:=actual_thermal_disturbed_step_bound x w
  have hm:=mul_le_mul_of_nonneg_left hx thermal_gain_positive_lt_one.1.le
  have hf:=(actual_invariant_radius_scalar_condition_iff_the_source_tube_radius radius).mpr hr
  linarith

theorem actual_unit_disk_invariant_under_every_source_disturbance (x w : E)
    (hx : ‖x‖≤1) (hw : ‖w‖≤1/20) : ‖actualThermalOperator x+w‖≤1 := by
  apply actual_tube_radius_invariant_step x w 1 hx hw
  exact (actual_invariant_radius_scalar_condition_iff_the_source_tube_radius 1).mp
    (by simpa using thermal_unit_disk_with_disturbance_budget)

theorem actual_every_disturbed_thermal_trajectory_has_the_literal_finite_envelope
    (x w : ℕ→E) (hstep : ∀ n,x (n+1)=actualThermalOperator (x n)+w n)
    (hw : ∀ n,‖w n‖≤1/20) :
    ∀ n,‖x n‖≤thermalGain^n*‖x 0‖+(1/20)*(1-thermalGain^n)/(1-thermalGain) := by
  have hs : ∀ n,|‖x (n+1)‖|≤thermalGain*|‖x n‖|+1/20 := by
    intro n
    rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (norm_nonneg _),hstep]
    exact (actual_thermal_disturbed_step_bound _ _).trans (add_le_add le_rfl (hw n))
  intro n
  have he:=BookApplications.tube_error_envelope (fun n=>‖x n‖) thermalGain (1/20)
    thermal_gain_positive_lt_one.1.le thermal_gain_positive_lt_one.2 hs n
  simp only [abs_of_nonneg (norm_nonneg _)] at he
  convert he using 1
  ring

theorem actual_every_disturbed_thermal_trajectory_is_eventually_inside_every_enlarged_tube
    (x w : ℕ→E) (hstep : ∀ n,x (n+1)=actualThermalOperator (x n)+w n)
    (hw : ∀ n,‖w n‖≤1/20) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ n in atTop,‖x n‖<actualTubeRadius+epsilon := by
  have hs : ∀ n,|‖x (n+1)‖|≤thermalGain*|‖x n‖|+1/20 := by
    intro n
    rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (norm_nonneg _),hstep]
    exact (actual_thermal_disturbed_step_bound _ _).trans (add_le_add le_rfl (hw n))
  simpa only [abs_of_nonneg (norm_nonneg _),actualTubeRadius] using
    CompleteModulesTheory.tube_ultimate_bound (fun n=>‖x n‖) thermalGain (1/20) epsilon
      thermal_gain_positive_lt_one.1.le thermal_gain_positive_lt_one.2 hepsilon hs

end SafeLearning.CompleteModulesThermalTubes
