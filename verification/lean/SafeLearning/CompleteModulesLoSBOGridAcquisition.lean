import SafeLearning.CompleteModulesLoSBOGridUpdates
import SafeLearning.CompleteModulesSafeOptEightPointPosteriors

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesLoSBOGridAcquisition
open CompleteModulesLoSBOGridUpdates CompleteModulesSafeOptEightPointPosteriors

def centeredCoordinate (i : Fin 11) : ℝ := sourceCoordinate i-1/2
def actualExampleKernel (i j : Fin 11) : ℝ := 1+centeredCoordinate i*centeredCoordinate j
def actualExampleMean (i : Fin 11) : ℝ :=
  actualGPMean actualExampleKernel (fun _ : Fin 1 => 5) 1 (fun _ => 7/5) i
def actualExampleVariance (i : Fin 11) : ℝ :=
  actualGPVariance actualExampleKernel (fun _ : Fin 1 => 5) 1 i
def actualExampleLower (i : Fin 11) : ℝ := actualExampleMean i-Real.sqrt (actualExampleVariance i)
def actualExampleUpper (i : Fin 11) : ℝ := actualExampleMean i+Real.sqrt (actualExampleVariance i)
def actualExampleWidth (i : Fin 11) : ℝ := actualExampleUpper i-actualExampleLower i
def actualExamplePotentialMaximizers : Set (Fin 11) :=
  {i | i ∈ sourceMultiFirst ∧ ∀ j ∈ sourceMultiFirst, actualExampleLower j≤actualExampleUpper i}

theorem actual_example_kernel_is_a_true_positive_semidefinite_kernel :
    (Matrix.of actualExampleKernel).PosSemidef := by
  have he : Matrix.of actualExampleKernel=
      Matrix.vecMulVec (fun _ : Fin 11 => (1:ℝ)) (star (fun _ : Fin 11 => (1:ℝ)))+
        Matrix.vecMulVec centeredCoordinate (star centeredCoordinate) := by
    ext i j
    simp [actualExampleKernel,Matrix.vecMulVec]
  rw [he]
  exact (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 11 => (1:ℝ))).add
    (Matrix.posSemidef_vecMulVec_self_star centeredCoordinate)

theorem actual_example_mean_and_variance_are_derived_from_the_real_one_observation_gp
    (i : Fin 11) : actualExampleMean i=7/10 ∧
      actualExampleVariance i=1/2+(centeredCoordinate i)^2 := by
  have hp := actual_one_observation_gp_matrix_formulas_are_the_true_scalar_mean_and_variance
    actualExampleKernel 5 i 1 (7/5)
  norm_num [actualExampleKernel,centeredCoordinate,sourceCoordinate] at hp
  refine ⟨hp.1,?_⟩
  unfold actualExampleVariance
  rw [hp.2]
  unfold centeredCoordinate sourceCoordinate
  ring

theorem actual_example_potential_maximizers_are_every_current_multi_constraint_safe_point :
    actualExamplePotentialMaximizers=sourceMultiFirst := by
  ext i
  constructor
  · exact fun hi => hi.1
  · intro hi
    refine ⟨hi,?_⟩
    intro j hj
    have hm := (actual_example_mean_and_variance_are_derived_from_the_real_one_observation_gp i).1
    have hmj := (actual_example_mean_and_variance_are_derived_from_the_real_one_observation_gp j).1
    unfold actualExampleLower actualExampleUpper
    rw [hm,hmj]
    linarith [Real.sqrt_nonneg (actualExampleVariance i),Real.sqrt_nonneg (actualExampleVariance j)]

theorem actual_example_width_is_twice_the_actual_posterior_standard_deviation (i : Fin 11) :
    actualExampleWidth i=2*Real.sqrt (1/2+(centeredCoordinate i)^2) := by
  unfold actualExampleWidth actualExampleUpper actualExampleLower
  rw [(actual_example_mean_and_variance_are_derived_from_the_real_one_observation_gp i).2]
  ring

theorem actual_both_source_endpoints_are_genuine_gp_width_acquisition_maximizers
    (expanders : Set (Fin 11)) (hexpanders : expanders ⊆ sourceMultiFirst) :
    (expanders ∪ actualExamplePotentialMaximizers)=sourceMultiFirst ∧
      (3:Fin 11) ∈ expanders ∪ actualExamplePotentialMaximizers ∧
      (7:Fin 11) ∈ expanders ∪ actualExamplePotentialMaximizers ∧
      (∀ i ∈ expanders ∪ actualExamplePotentialMaximizers,
        actualExampleWidth i≤actualExampleWidth 3 ∧ actualExampleWidth i≤actualExampleWidth 7) := by
  have he : expanders ∪ actualExamplePotentialMaximizers=sourceMultiFirst := by
    rw [actual_example_potential_maximizers_are_every_current_multi_constraint_safe_point]
    exact union_eq_right.mpr hexpanders
  rw [he]
  refine ⟨rfl,?_,?_,?_⟩
  · exact actual_source_second_constraint_intersection_excludes_the_planned_point_nine_query.2.2.2.1
  · exact actual_source_second_constraint_intersection_excludes_the_planned_point_nine_query.2.2.2.2
  · intro i hi
    have hv : 1/2+(centeredCoordinate i)^2≤(27/50:ℝ) := by
      have hh : (3:ℕ) ≤ i.val ∧ i.val ≤ 7 := by
        rw [actual_source_second_constraint_intersection_excludes_the_planned_point_nine_query.2.1] at hi
        exact hi
      fin_cases i <;>
        norm_num [centeredCoordinate,sourceCoordinate] at *
    have hs := Real.sqrt_le_sqrt hv
    rw [actual_example_width_is_twice_the_actual_posterior_standard_deviation,
      actual_example_width_is_twice_the_actual_posterior_standard_deviation,
      actual_example_width_is_twice_the_actual_posterior_standard_deviation]
    rw [show (1/2:ℝ)+(centeredCoordinate 3)^2=27/50 by norm_num [centeredCoordinate,sourceCoordinate],
      show (1/2:ℝ)+(centeredCoordinate 7)^2=27/50 by norm_num [centeredCoordinate,sourceCoordinate]]
    constructor <;> exact mul_le_mul_of_nonneg_left hs (by norm_num)

end SafeLearning.CompleteModulesLoSBOGridAcquisition
