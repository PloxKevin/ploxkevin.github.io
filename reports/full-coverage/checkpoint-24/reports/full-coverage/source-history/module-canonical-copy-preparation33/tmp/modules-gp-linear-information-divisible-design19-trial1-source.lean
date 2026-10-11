import SafeLearning.CompleteModulesGPLinearInformationMaxima
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationDivisibleDesign
open CompleteModulesGPLinearInformationBounds CompleteModulesGPLinearInformationDesigns
  CompleteModulesGPLinearInformationMaxima
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

theorem actual_relabeling_the_samples_preserves_the_true_feature_gram
    {S : Type*} [Fintype S] (X : Matrix S D ℝ) (e : T ≃ S) :
    (X.submatrix e id)ᵀ*X.submatrix e id=Xᵀ*X := by
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv]
  exact Matrix.submatrix_id_id _

theorem actual_dimension_divisibility_constructs_unit_inputs_with_the_uniform_gram
    [Nonempty D] (hDiv : Fintype.card D ∣ Fintype.card T) :
    ∃ X : Matrix T D ℝ,
      (∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖=1) ∧
      Xᵀ*X=((Fintype.card T:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ) := by
  obtain ⟨m,hm⟩ := hDiv
  have hc : Fintype.card T=Fintype.card (Fin m × D) := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using hm
  let e : T ≃ Fin m × D := Fintype.equivOfCardEq hc
  let X : Matrix T D ℝ := (cycleDesign m).submatrix e id
  have hn : (Fintype.card D:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : (Fintype.card T:ℝ)/(Fintype.card D:ℝ)=(m:ℝ) := by
    rw [hm,Nat.cast_mul]
    field_simp
  refine ⟨X,?_,?_⟩
  · intro t
    exact actual_cycling_inputs_have_unit_euclidean_norm m (e t)
  · change ((cycleDesign m).submatrix e id)ᵀ*(cycleDesign m).submatrix e id=_
    rw [actual_relabeling_the_samples_preserves_the_true_feature_gram,
      actual_cycle_design_gram_is_the_sample_per_dimension_times_identity,ha]

theorem actual_every_positive_dimension_dividing_any_sample_count_attains_the_source_maximum
    [Nonempty D] (hDiv : Fintype.card D ∣ Fintype.card T)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    IsGreatest (admissibleInformationValues T D lambda)
      ((Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ)))) := by
  obtain ⟨X,hX,hGram⟩ := actual_dimension_divisibility_constructs_unit_inputs_with_the_uniform_gram hDiv
  exact actual_any_true_unit_norm_tight_frame_attains_the_dimension_bound X lambda hlambda hX hGram

theorem actual_divisible_design_maximum_is_the_supremum_over_all_designs
    [Nonempty D] (hDiv : Fintype.card D ∣ Fintype.card T)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    sSup (admissibleInformationValues T D lambda)=
      (Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) :=
  (actual_every_positive_dimension_dividing_any_sample_count_attains_the_source_maximum
    hDiv lambda hlambda).csSup_eq

end SafeLearning.CompleteModulesGPLinearInformationDivisibleDesign
