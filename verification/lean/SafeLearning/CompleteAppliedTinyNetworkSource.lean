import SafeLearning.CompleteAppliedTinyNetworkGeometry
import SafeLearning.CompleteAppliedTinyNetworkGains

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedTinyNetworkSource
open SafeLearning.CompleteAppliedTinyNetwork
open SafeLearning.CompleteAppliedTinyNetworkGeometry
open SafeLearning.CompleteAppliedTinyNetworkGains

theorem actual_perpendicular_foot_is_on_the_closest_boundary_branch :
    point (-2) 0+(2:ℝ)•point 1 1=point 0 2 ∧
    (point 0 2) 0+(point 0 2) 1=2 ∧ (point 0 2) 0≤(point 0 2) 1 ∧
    network (point 0 2)=0 := by
  refine ⟨?_,by norm_num [point],by norm_num [point],
    actual_question_point_to_literal_nearest_boundary_squared_distance.1⟩
  ext i;fin_cases i <;> norm_num [point]

theorem actual_local_box_is_exactly_the_unit_coordinate_ball (x : E) :
    ((-3:ℝ)≤x 0 ∧ x 0≤-1) ∧ ((-1:ℝ)≤x 1 ∧ x 1≤1) ↔
    |x 0-(point (-2) 0) 0|≤1 ∧ |x 1-(point (-2) 0) 1|≤1 := by
  have hc0 : (point (-2) 0) 0=(-2:ℝ) := rfl
  have hc1 : (point (-2) 0) 1=(0:ℝ) := rfl
  rw [hc0,hc1,sub_neg_eq_add,sub_zero,abs_le,abs_le]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

theorem actual_pixel_center_and_certified_radius_have_the_correct_input_space
    (pixel : E) (hpixel : ‖pixel-point (-1) 0‖<1/(2*Real.sqrt 10)) :
    (2:ℝ)•point (-1) 0=point (-2) 0 ∧ network ((2:ℝ)•pixel)<0 := by
  have hc : (2:ℝ)•point (-1) 0=point (-2) 0 := by
    ext i;fin_cases i <;> norm_num [point]
  refine ⟨hc,?_⟩
  apply actual_global_radius_certifies_every_strictly_inside_perturbation
  have hd := (actual_pixel_normalization_doubles_distances_and_composite_gain pixel (point (-1) 0)).1
  rw [hc] at hd
  rw [hd]
  have hp : 0<Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have h := (lt_div_iff₀ (by positivity : (0:ℝ)<2*Real.sqrt 10)).mp hpixel
  apply (lt_div_iff₀ hp).mpr
  nlinarith

theorem actual_true_boundary_and_certificate_ratios_are_the_exact_source_quantities :
    (2*Real.sqrt 2)/(1/Real.sqrt 10)=(2*Real.sqrt 2)*Real.sqrt 10 ∧
    (1:ℝ)/(1/Real.sqrt 10)=Real.sqrt 10 ∧
    (1/Real.sqrt 10)*(1/2)=1/(2*Real.sqrt 10) := by
  have hs : Real.sqrt 10≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<10)).ne'
  field_simp
  simp

end SafeLearning.CompleteAppliedTinyNetworkSource
