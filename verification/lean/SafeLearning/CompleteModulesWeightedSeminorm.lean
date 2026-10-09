import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesWeightedSeminorm
open CompleteModulesLipSDP
variable {I : Type*} [Fintype I] [DecidableEq I]

def actualWeightedMagnitude (weight : Matrix I I ℝ) (vector : I → ℝ) : ℝ :=
  Real.sqrt (quadratic weight vector)

theorem actual_positive_semidefinite_weight_has_actual_gram_factor
    (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) :
    ∃ factor : Matrix I I ℝ,weight=factorᵀ*factor := by
  obtain ⟨factor,hfactor⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hweight.nonneg
  have hs : star factor=factorᵀ := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
  rw [hs] at hfactor
  exact ⟨factor,hfactor⟩

theorem actual_weighted_magnitude_is_norm_of_gram_image
    (weight factor : Matrix I I ℝ) (hfactor : weight=factorᵀ*factor) (vector : I → ℝ) :
    actualWeightedMagnitude weight vector=‖WithLp.toLp 2 (factor *ᵥ vector)‖ := by
  rw [actualWeightedMagnitude,hfactor,quadratic_gram,← squared_norm_of_coordinates]
  exact Real.sqrt_sq (norm_nonneg _)

theorem actual_weighted_magnitude_triangle_inequality
    (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) (first second : I → ℝ) :
    actualWeightedMagnitude weight (first+second) ≤
      actualWeightedMagnitude weight first+actualWeightedMagnitude weight second := by
  obtain ⟨factor,hfactor⟩ := actual_positive_semidefinite_weight_has_actual_gram_factor weight hweight
  simp only [actual_weighted_magnitude_is_norm_of_gram_image weight factor hfactor,Matrix.mulVec_add,WithLp.toLp_add]
  exact norm_add_le _ _

theorem actual_weighted_magnitude_is_absolutely_homogeneous
    (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) (scalar : ℝ) (vector : I → ℝ) :
    actualWeightedMagnitude weight (scalar • vector)=|scalar| * actualWeightedMagnitude weight vector := by
  obtain ⟨factor,hfactor⟩ := actual_positive_semidefinite_weight_has_actual_gram_factor weight hweight
  simp only [actual_weighted_magnitude_is_norm_of_gram_image weight factor hfactor,Matrix.mulVec_smul,
    WithLp.toLp_smul,norm_smul,Real.norm_eq_abs]

def actualWeightedSeminorm (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) :
    Seminorm ℝ (I → ℝ) where
  toFun := actualWeightedMagnitude weight
  map_zero' := by simp [actualWeightedMagnitude,quadratic]
  add_le' := actual_weighted_magnitude_triangle_inequality weight hweight
  neg' := by
    intro vector
    have h := actual_weighted_magnitude_is_absolutely_homogeneous weight hweight (-1) vector
    simpa using h
  smul' := by
    intro scalar vector
    simpa only [Real.norm_eq_abs] using actual_weighted_magnitude_is_absolutely_homogeneous weight hweight scalar vector

theorem actual_weighted_magnitude_vanishes_iff_in_matrix_kernel
    (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) (vector : I → ℝ) :
    actualWeightedMagnitude weight vector=0 ↔ weight *ᵥ vector=0 := by
  have hp : 0 ≤ quadratic weight vector := by
    simpa only [quadratic,star_trivial] using hweight.dotProduct_mulVec_nonneg vector
  rw [actualWeightedMagnitude,Real.sqrt_eq_zero hp]
  simpa only [quadratic,star_trivial] using (hweight.dotProduct_mulVec_zero_iff (x := vector))

theorem actual_positive_definite_weighted_magnitude_separates_zero
    (weight : Matrix I I ℝ) (hweight : weight.PosDef) (vector : I → ℝ) :
    actualWeightedMagnitude weight vector=0 ↔ vector=0 := by
  rw [actual_weighted_magnitude_vanishes_iff_in_matrix_kernel weight hweight.posSemidef]
  exact ⟨fun h => Matrix.mulVec_injective_of_det_ne_zero hweight.det_pos.ne' (by simpa using h),
    fun h => by simp [h]⟩

def actualPositiveDefiniteWeightedGroupNorm (weight : Matrix I I ℝ) (hweight : weight.PosDef) :
    AddGroupNorm (I → ℝ) where
  toAddGroupSeminorm := (actualWeightedSeminorm weight hweight.posSemidef).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' := fun vector =>
    (actual_positive_definite_weighted_magnitude_separates_zero weight hweight vector).mp

theorem actual_singular_positive_semidefinite_weight_has_nonzero_zero_magnitude
    (weight : Matrix I I ℝ) (hweight : weight.PosSemidef) (hsingular : weight.det=0) :
    ∃ vector : I → ℝ,vector≠0 ∧ actualWeightedMagnitude weight vector=0 := by
  obtain ⟨vector,hvector,hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hsingular
  exact ⟨vector,hvector,(actual_weighted_magnitude_vanishes_iff_in_matrix_kernel weight hweight vector).mpr hkernel⟩

end SafeLearning.CompleteModulesWeightedSeminorm
