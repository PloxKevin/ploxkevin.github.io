import SafeLearning.CompleteModulesLoSBOGridAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLoSBOGridMultiAcquisition
open CompleteModulesLoSBOGridAcquisition CompleteModulesLoSBOGridUpdates
open CompleteModulesSafeOptEightPointPosteriors

def actualIndexedLabel (index : Fin 3) : ℝ := ![7/5,7/5,7/20] index
def actualIndexedMean (index : Fin 3) (i : Fin 11) : ℝ :=
  actualGPMean actualExampleKernel (fun _ : Fin 1 => 5) 1 (fun _ => actualIndexedLabel index) i
def actualIndexedVariance (_index : Fin 3) (i : Fin 11) : ℝ :=
  actualGPVariance actualExampleKernel (fun _ : Fin 1 => 5) 1 i
def actualIndexedWidth (index : Fin 3) (i : Fin 11) : ℝ :=
  (actualIndexedMean index i+Real.sqrt (actualIndexedVariance index i))-
    (actualIndexedMean index i-Real.sqrt (actualIndexedVariance index i))
def actualMultiAcquisitionWidth (i : Fin 11) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun index : Fin 3 => actualIndexedWidth index i)

theorem actual_objective_and_both_constraint_gps_use_the_true_source_labels_and_equal_variances
    (index : Fin 3) (i : Fin 11) :
    actualIndexedLabel 0=7/5 ∧ actualIndexedLabel 1=7/5 ∧ actualIndexedLabel 2=7/20 ∧
      actualIndexedVariance index i=1/2+(centeredCoordinate i)^2 := by
  refine ⟨by norm_num [actualIndexedLabel],by norm_num [actualIndexedLabel],
    by norm_num [actualIndexedLabel],?_⟩
  exact (actual_example_mean_and_variance_are_derived_from_the_real_one_observation_gp i).2

theorem actual_each_indexed_gp_width_equals_the_existing_true_example_width
    (index : Fin 3) (i : Fin 11) : actualIndexedWidth index i=actualExampleWidth i := by
  unfold actualIndexedWidth actualIndexedVariance actualExampleWidth actualExampleUpper
    actualExampleLower actualExampleVariance
  ring

theorem actual_maximum_across_all_three_gp_widths_is_exactly_the_example_width
    (i : Fin 11) : actualMultiAcquisitionWidth i=actualExampleWidth i := by
  unfold actualMultiAcquisitionWidth
  simp_rw [actual_each_indexed_gp_width_equals_the_existing_true_example_width]
  exact Finset.sup'_const _ _

theorem actual_source_endpoints_maximize_the_real_multiconstraint_acquisition
    (expanders : Set (Fin 11)) (hexpanders : expanders ⊆ sourceMultiFirst) :
    (3:Fin 11) ∈ expanders ∪ actualExamplePotentialMaximizers ∧
      (7:Fin 11) ∈ expanders ∪ actualExamplePotentialMaximizers ∧
      ∀ i ∈ expanders ∪ actualExamplePotentialMaximizers,
        actualMultiAcquisitionWidth i≤actualMultiAcquisitionWidth 3 ∧
          actualMultiAcquisitionWidth i≤actualMultiAcquisitionWidth 7 := by
  have h := actual_both_source_endpoints_are_genuine_gp_width_acquisition_maximizers expanders hexpanders
  refine ⟨h.2.1,h.2.2.1,?_⟩
  intro i hi
  simp_rw [actual_maximum_across_all_three_gp_widths_is_exactly_the_example_width]
  exact h.2.2.2 i hi

end SafeLearning.CompleteModulesLoSBOGridMultiAcquisition
