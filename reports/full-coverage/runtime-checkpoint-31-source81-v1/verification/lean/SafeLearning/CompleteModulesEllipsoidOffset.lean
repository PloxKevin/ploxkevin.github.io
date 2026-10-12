import SafeLearning.CompleteModulesEllipsoidRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Matrix
namespace SafeLearning.CompleteModulesEllipsoidOffset
open CompleteModulesEllipsoidRow
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem actual_negative_ellipsoid_vector_has_the_same_energy
    (storage : Matrix n n ℝ) (vector : n→ℝ) :
    (-vector) ⬝ᵥ (storage *ᵥ (-vector))=vector ⬝ᵥ (storage *ᵥ vector) := by
  rw [Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg]

def actualAffineIntervalContainment (storage : Matrix n n ℝ) (row : n→ℝ)
    (left center right : ℝ) : Prop :=
  ∀ vector : n→ℝ,vector ⬝ᵥ (storage *ᵥ vector)≤1→
    center+row ⬝ᵥ vector∈Icc left right

theorem actual_affine_interval_containment_iff_both_endpoint_margin_bounds
    (storage : Matrix n n ℝ) (row : n→ℝ) (left center right : ℝ) :
    actualAffineIntervalContainment storage row left center right ↔
      (∀ vector : n→ℝ,vector ⬝ᵥ (storage *ᵥ vector)≤1→|row ⬝ᵥ vector|≤right-center) ∧
      (∀ vector : n→ℝ,vector ⬝ᵥ (storage *ᵥ vector)≤1→|row ⬝ᵥ vector|≤center-left) := by
  constructor
  · intro h
    constructor <;> intro vector hv
    all_goals
      have hp := h vector hv
      have hn := h (-vector) (by rwa [actual_negative_ellipsoid_vector_has_the_same_energy])
      rw [dotProduct_neg] at hn
      apply abs_le.mpr
      constructor <;> linarith [hp.1,hp.2,hn.1,hn.2]
  · rintro ⟨hr,hl⟩ vector hv
    have hp := abs_le.mp (hr vector hv)
    have hn := abs_le.mp (hl vector hv)
    constructor <;> linarith [hp.2,hn.1]

theorem actual_affine_interval_containment_iff_the_two_true_schur_lmis
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n→ℝ)
    (left center right : ℝ) (hl : left≤center) (hr : center≤right) :
    actualAffineIntervalContainment storage row left center right ↔
      (actualRowContainmentBlock storage row (right-center)).PosSemidef ∧
      (actualRowContainmentBlock storage row (center-left)).PosSemidef := by
  rw [actual_affine_interval_containment_iff_both_endpoint_margin_bounds,
    actual_row_interval_containment_iff_the_true_source_schur_lmi storage hs row
      (right-center) (sub_nonneg.mpr hr),
    actual_row_interval_containment_iff_the_true_source_schur_lmi storage hs row
      (center-left) (sub_nonneg.mpr hl)]

theorem actual_affine_interval_containment_iff_the_smaller_margin_schur_lmi
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n→ℝ)
    (left center right : ℝ) (hl : left≤center) (hr : center≤right) :
    actualAffineIntervalContainment storage row left center right ↔
      (actualRowContainmentBlock storage row (min (right-center) (center-left))).PosSemidef := by
  rw [←actual_row_interval_containment_iff_the_true_source_schur_lmi storage hs row
    (min (right-center) (center-left)) (le_min (sub_nonneg.mpr hr) (sub_nonneg.mpr hl)),
    actual_affine_interval_containment_iff_both_endpoint_margin_bounds]
  constructor
  · rintro ⟨h1,h2⟩ vector hv
    exact le_min (h1 vector hv) (h2 vector hv)
  · intro h
    exact ⟨fun vector hv => (h vector hv).trans (min_le_left _ _),
      fun vector hv => (h vector hv).trans (min_le_right _ _)⟩

end SafeLearning.CompleteModulesEllipsoidOffset
