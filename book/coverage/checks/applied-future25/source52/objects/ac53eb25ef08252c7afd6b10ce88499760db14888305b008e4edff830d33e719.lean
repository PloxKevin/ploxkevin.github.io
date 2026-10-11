import SafeLearning.CompleteModulesTanhOffsetEndpoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Matrix
namespace SafeLearning.CompleteModulesTanhOffsetQC
open CompleteModulesTanhOffsetEndpoints CompleteModulesTanhChords
open CompleteModulesTanhRefinement CompleteModulesLipSDP CompleteModulesDiagonalQC

def sourceEndpointLower (left center right : ℝ) : ℝ :=
  min (offsetSlope right center) (offsetSlope left center)

theorem actual_source_left_endpoint_fraction_is_the_same_chord (left center : ℝ) :
    (Real.tanh center-Real.tanh left)/(center-left)=offsetSlope left center := by
  dsimp [offsetSlope]
  rw [←neg_sub (Real.tanh left) (Real.tanh center),←neg_sub left center,neg_div_neg_eq]

theorem actual_source_endpoint_lower_is_the_literal_minimum (left center right : ℝ) :
    sourceEndpointLower left center right=
      min ((Real.tanh right-Real.tanh center)/(right-center))
        ((Real.tanh center-Real.tanh left)/(center-left)) := by
  rw [actual_source_left_endpoint_fraction_is_the_same_chord left center]
  rfl

theorem actual_source_endpoint_lower_is_positive_and_at_most_one
    (left center right : ℝ) (hl : left<center) (hr : center<right) :
    0<sourceEndpointLower left center right ∧ sourceEndpointLower left center right≤1 := by
  have hleft := actual_tanh_chord_quotient_is_positive_and_at_most_one left center hl.ne
  have hright := actual_tanh_chord_quotient_is_positive_and_at_most_one right center hr.ne'
  exact ⟨lt_min hright.1 hleft.1,(min_le_left _ _).trans hright.2⟩

theorem actual_all_offset_points_satisfy_the_literal_endpoint_sector_qc
    (left center right point : ℝ) (hl : left<center) (hr : center<right)
    (hp : point∈Icc left right) :
    0≤quadratic (actualSectorQCMatrix (sourceEndpointLower left center right) 1)
      ![point-center,Real.tanh point-Real.tanh center] := by
  rw [actual_sector_qc_matrix_has_the_literal_quadratic]
  have hu := (actual_source_endpoint_lower_is_positive_and_at_most_one left center right hl hr).2
  apply (scalar_qc_iff_admissible_chord _ 1 _ _ hu).mpr
  by_cases he : point=center
  · subst point
    exact ⟨sourceEndpointLower left center right,le_rfl,hu,by simp⟩
  · exact ⟨offsetSlope point center,
      actual_offset_chords_have_the_literal_minimum_endpoint_lower_bound left center right point hl hr hp he,
      (actual_tanh_chord_quotient_is_positive_and_at_most_one point center he).2,
      (div_mul_cancel₀ _ (sub_ne_zero.mpr he)).symm⟩

theorem actual_shifted_deviation_satisfies_the_same_literal_offset_qc
    (left center right deviation : ℝ) (hl : left<center) (hr : center<right)
    (hd : center+deviation∈Icc left right) :
    0≤quadratic (actualSectorQCMatrix (sourceEndpointLower left center right) 1)
      ![deviation,actualOffsetTanh center deviation] := by
  simpa only [add_sub_cancel_left,actualOffsetTanh] using
    actual_all_offset_points_satisfy_the_literal_endpoint_sector_qc
      left center right (center+deviation) hl hr hd

theorem actual_endpoint_minimum_is_the_greatest_offset_lower_slope
    (left center right : ℝ) (hl : left<center) (hr : center<right) :
    IsGreatest {lower : ℝ | ∀ point∈Icc left right,point≠center→lower≤offsetSlope point center}
      (sourceEndpointLower left center right) := by
  refine ⟨fun point hp he =>
    actual_offset_chords_have_the_literal_minimum_endpoint_lower_bound left center right point hl hr hp he,?_⟩
  intro lower h
  exact le_min (h right ⟨hl.le.trans hr.le,le_rfl⟩ hr.ne')
    (h left ⟨le_rfl,hl.le.trans hr.le⟩ hl.ne)

theorem actual_endpoint_minimum_is_attained_by_an_allowed_distinct_endpoint
    (left center right : ℝ) (hl : left<center) (hr : center<right) :
    ∃ point∈Icc left right,point≠center ∧
      offsetSlope point center=sourceEndpointLower left center right := by
  by_cases h : offsetSlope right center≤offsetSlope left center
  · exact ⟨right,⟨hl.le.trans hr.le,le_rfl⟩,hr.ne',by simp [sourceEndpointLower,min_eq_left h]⟩
  · exact ⟨left,⟨le_rfl,hl.le.trans hr.le⟩,hl.ne,by simp [sourceEndpointLower,min_eq_right (le_of_not_ge h)]⟩

section LiteralQCDefinitions
variable {coordinate : Type*} [Fintype coordinate]

def actualSymmetricQCSet
    (constraints : Set (Matrix (Sum coordinate coordinate) (Sum coordinate coordinate) ℝ)) : Prop :=
  ∀ constraint∈constraints,constraint.IsSymm

def actualIncrementalQC (activation : (coordinate→ℝ)→coordinate→ℝ)
    (constraints : Set (Matrix (Sum coordinate coordinate) (Sum coordinate coordinate) ℝ)) : Prop :=
  ∀ constraint∈constraints,∀ first second,
    0≤quadratic constraint (Sum.elim (first-second) (activation first-activation second))

def actualFixedPointQCOn (activation : (coordinate→ℝ)→coordinate→ℝ)
    (constraints : Set (Matrix (Sum coordinate coordinate) (Sum coordinate coordinate) ℝ))
    (center : coordinate→ℝ) (domain : Set (coordinate→ℝ)) : Prop :=
  ∀ constraint∈constraints,∀ point∈domain,
    0≤quadratic constraint (Sum.elim (point-center) (activation point-activation center))

theorem actual_incremental_constraints_specialize_to_every_fixed_point_and_local_domain
    (activation : (coordinate→ℝ)→coordinate→ℝ)
    (constraints : Set (Matrix (Sum coordinate coordinate) (Sum coordinate coordinate) ℝ))
    (center : coordinate→ℝ) (domain : Set (coordinate→ℝ))
    (h : actualIncrementalQC activation constraints) :
    actualFixedPointQCOn activation constraints center domain := by
  intro constraint hc point _
  exact h constraint hc point center

end LiteralQCDefinitions
end SafeLearning.CompleteModulesTanhOffsetQC
