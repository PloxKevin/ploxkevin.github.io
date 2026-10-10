import SafeLearning.CompleteModulesGPLinearInformationDesigns
import SafeLearning.CompleteModulesGPLinearInformationStrictness
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationMaxima
open CompleteModulesGPLinearInformationBounds CompleteModulesGPLinearInformationDesigns
  CompleteModulesGPLinearInformationStrictness
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

def admissibleInformationValues (T D : Type*) [Fintype T] [Fintype D]
    [DecidableEq D] (lambda : ℝ) : Set ℝ :=
  {v | ∃ X : Matrix T D ℝ,
    (∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1) ∧
      v=information (Xᵀ*X) lambda}

theorem actual_maximization_over_all_unit_ball_designs_preserves_the_dimension_bound
    [Nonempty D] (lambda : ℝ) (hlambda : 0 < lambda) :
    (Fintype.card D:ℝ)/2*Real.log
      (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) ∈
        upperBounds (admissibleInformationValues T D lambda) := by
  rintro v ⟨X,hX,rfl⟩
  exact actual_linear_design_information_has_the_dimension_trace_bound X lambda hlambda hX

theorem actual_all_unit_ball_information_values_form_a_nonempty_bounded_above_set
    [Nonempty D] (lambda : ℝ) (hlambda : 0 < lambda) :
    (admissibleInformationValues T D lambda).Nonempty ∧
      BddAbove (admissibleInformationValues T D lambda) := by
  constructor
  · refine ⟨0,0,?_,?_⟩
    · simp
    · simp [information]
  · exact ⟨_,actual_maximization_over_all_unit_ball_designs_preserves_the_dimension_bound lambda hlambda⟩

theorem actual_supremum_of_all_admissible_design_information_has_the_source_bound
    [Nonempty D] (lambda : ℝ) (hlambda : 0 < lambda) :
    sSup (admissibleInformationValues T D lambda) ≤
      (Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) := by
  exact csSup_le (actual_all_unit_ball_information_values_form_a_nonempty_bounded_above_set
    lambda hlambda).1 (actual_maximization_over_all_unit_ball_designs_preserves_the_dimension_bound
      lambda hlambda)

theorem actual_any_true_unit_norm_tight_frame_attains_the_dimension_bound
    [Nonempty D] (X : Matrix T D ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖=1)
    (hGram : Xᵀ*X=((Fintype.card T:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ)) :
    IsGreatest (admissibleInformationValues T D lambda)
      ((Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ)))) := by
  have he : information (Xᵀ*X) lambda=(Fintype.card D:ℝ)/2*Real.log
      (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) := by
    rw [hGram,actual_scalar_identity_information_is_the_source_closed_form _ lambda hlambda
      (by positivity)]
    congr 3
    field_simp
  constructor
  · exact ⟨X,fun t => (hX t).le,he.symm⟩
  · exact actual_maximization_over_all_unit_ball_designs_preserves_the_dimension_bound lambda hlambda

theorem actual_cycling_design_proves_the_greatest_value_over_every_competing_design
    [Nonempty D] (m : ℕ) (lambda : ℝ) (hlambda : 0 < lambda) :
    IsGreatest (admissibleInformationValues (Fin m × D) D lambda)
      ((Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card (Fin m × D):ℝ)/(lambda*(Fintype.card D:ℝ)))) := by
  constructor
  · exact ⟨cycleDesign m,fun t => (actual_cycling_inputs_have_unit_euclidean_norm m t).le,
      (actual_cycling_design_attains_the_dimension_bound_when_dimension_divides_sample_count
        m lambda hlambda).symm⟩
  · exact actual_maximization_over_all_unit_ball_designs_preserves_the_dimension_bound lambda hlambda

theorem actual_orthonormal_design_proves_the_greatest_small_sample_value
    [Nonempty T] (e : T ↪ D) (lambda : ℝ) (hlambda : 0 < lambda) :
    IsGreatest (admissibleInformationValues T D lambda)
      ((Fintype.card T:ℝ)/2*Real.log (1+1/lambda)) := by
  constructor
  · exact ⟨orthonormalDesign e,
      fun t => (actual_embedded_orthonormal_inputs_have_unit_euclidean_norm e t).le,
      (actual_orthonormal_design_information_is_the_source_small_sample_maximum e lambda hlambda).symm⟩
  · rintro v ⟨X,hX,rfl⟩
    exact actual_every_unit_ball_design_has_the_sample_dimension_information_bound X lambda hlambda hX

theorem actual_smaller_positive_sample_count_has_an_attaining_orthonormal_design
    [Nonempty T] (hOrder : Fintype.card T ≤ Fintype.card D)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    IsGreatest (admissibleInformationValues T D lambda)
      ((Fintype.card T:ℝ)/2*Real.log (1+1/lambda)) := by
  obtain ⟨e⟩ := Fintype.card_le_iff.mp hOrder
  exact actual_orthonormal_design_proves_the_greatest_small_sample_value e lambda hlambda

end SafeLearning.CompleteModulesGPLinearInformationMaxima
