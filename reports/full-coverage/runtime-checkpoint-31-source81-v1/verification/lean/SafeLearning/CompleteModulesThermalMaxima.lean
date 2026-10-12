import SafeLearning.CompleteModulesThermalEigen

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesThermalMaxima
open CompleteModulesThermalTubes

def actualStartupBox : Set E := {x | ∀ index, |x index| ≤ 7/10}
def actualStartupCorner : E := WithLp.toLp 2 ![7/10,7/10]

theorem actual_source_allowed_startup_corner_attains_the_exact_energy_and_radius :
    actualStartupCorner ∈ actualStartupBox ∧
    ‖actualStartupCorner‖^2 = 49/50 ∧
    ‖actualStartupCorner‖ = Real.sqrt (49/50) := by
  refine ⟨?_,?_,?_⟩
  · intro index
    fin_cases index <;> norm_num [actualStartupCorner]
  · rw [actual_thermal_euclidean_norm_squared]
    norm_num [actualStartupCorner]
  · rw [actual_thermal_euclidean_norm_is_the_literal_square_root]
    norm_num [CompleteModulesDynamics.l2,actualStartupCorner]

theorem actual_largest_startup_energy_is_the_printed_point_nine_eight :
    IsGreatest ((fun x : E => ‖x‖^2) '' actualStartupBox) (49/50) := by
  obtain ⟨hx,he,hr⟩ := actual_source_allowed_startup_corner_attains_the_exact_energy_and_radius
  refine ⟨⟨actualStartupCorner,hx,he⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (actual_startup_box_has_the_literal_energy_and_radius_bound x hx).1

theorem actual_largest_startup_radius_is_the_printed_square_root :
    IsGreatest ((fun x : E => ‖x‖) '' actualStartupBox) (Real.sqrt (49/50)) := by
  obtain ⟨hx,he,hr⟩ := actual_source_allowed_startup_corner_attains_the_exact_energy_and_radius
  refine ⟨⟨actualStartupCorner,hx,hr⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (actual_startup_box_has_the_literal_energy_and_radius_bound x hx).2.1

end SafeLearning.CompleteModulesThermalMaxima
