import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesCayley

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualCayley (skew : Matrix N N ℝ) : Matrix N N ℝ :=
  (1-skew)*(1+skew)⁻¹

theorem actual_skew_cayley_denominator_gram_is_positive
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) :
    ((1+skew)ᵀ*(1+skew)).PosDef := by
  have he : (1+skew)ᵀ*(1+skew)=(1 : Matrix N N ℝ)+skewᵀ*skew := by
    rw [Matrix.transpose_add,Matrix.transpose_one,hskew]
    noncomm_ring
  rw [he]
  apply Matrix.PosDef.one.add_posSemidef
  simpa using Matrix.posSemidef_conjTranspose_mul_self skew

theorem actual_skew_cayley_denominator_is_invertible
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) : IsUnit (1+skew) := by
  apply (Matrix.isUnit_iff_isUnit_det (1+skew)).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  have h := (actual_skew_cayley_denominator_gram_is_positive skew hskew).det_pos
  rw [Matrix.det_mul,Matrix.det_transpose,hdet] at h
  norm_num at h

theorem actual_skew_cayley_numerator_is_transposed_denominator
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) : (1+skew)ᵀ=1-skew := by
  rw [Matrix.transpose_add,Matrix.transpose_one,hskew,sub_eq_add_neg]

theorem actual_skew_cayley_numerator_is_invertible
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) : IsUnit (1-skew) := by
  rw [← actual_skew_cayley_numerator_is_transposed_denominator skew hskew,
    Matrix.isUnit_transpose]
  exact actual_skew_cayley_denominator_is_invertible skew hskew

theorem actual_cayley_is_orthogonal
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) :
    (actualCayley skew)ᵀ*actualCayley skew=1 := by
  letI := (actual_skew_cayley_denominator_is_invertible skew hskew).invertible
  letI := (actual_skew_cayley_numerator_is_invertible skew hskew).invertible
  have hn : (1-skew)ᵀ=1+skew := by
    rw [Matrix.transpose_sub,Matrix.transpose_one,hskew,sub_neg_eq_add]
  have hc : (1+skew)*(1-skew)=(1-skew)*(1+skew) := by noncomm_ring
  unfold actualCayley
  rw [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,
    actual_skew_cayley_numerator_is_transposed_denominator skew hskew,hn]
  calc
    _ = (1-skew)⁻¹*((1+skew)*(1-skew))*(1+skew)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1-skew)⁻¹*((1-skew)*(1+skew))*(1+skew)⁻¹ := by rw [hc]
    _ = 1 := by rw [← Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.one_mul,
      Matrix.mul_inv_of_invertible]

theorem actual_cayley_has_determinant_one
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) : (actualCayley skew).det=1 := by
  have hunit := actual_skew_cayley_denominator_is_invertible skew hskew
  have hdet := ((1+skew).isUnit_iff_isUnit_det.mp hunit)
  have he : (1-skew).det=(1+skew).det := by
    rw [← actual_skew_cayley_numerator_is_transposed_denominator skew hskew,Matrix.det_transpose]
  unfold actualCayley
  rw [Matrix.det_mul,he,mul_comm]
  exact Matrix.det_nonsing_inv_mul_det (1+skew) hdet

theorem actual_cayley_plus_identity_is_twice_inverse
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) :
    actualCayley skew+1=(2:ℝ) • (1+skew)⁻¹ := by
  letI := (actual_skew_cayley_denominator_is_invertible skew hskew).invertible
  unfold actualCayley
  have he : (1 : Matrix N N ℝ)=(1+skew)*(1+skew)⁻¹ :=
    (Matrix.mul_inv_of_invertible (1+skew)).symm
  calc
    _ = (1-skew)*(1+skew)⁻¹+(1+skew)*(1+skew)⁻¹ := congrArg (_+·) he
    _ = ((1-skew)+(1+skew))*(1+skew)⁻¹ := by noncomm_ring
    _ = (2:ℝ) • (1+skew)⁻¹ := by
      have hsum : (1-skew)+(1+skew)=(2:ℝ) • (1 : Matrix N N ℝ) := by module
      rw [hsum,Matrix.smul_mul,Matrix.one_mul]

theorem actual_cayley_plus_identity_is_invertible
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) : IsUnit (actualCayley skew+1) := by
  rw [actual_cayley_plus_identity_is_twice_inverse skew hskew]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_smul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  · exact Matrix.isUnit_nonsing_inv_det _
      ((1+skew).isUnit_iff_isUnit_det.mp (actual_skew_cayley_denominator_is_invertible skew hskew))

theorem actual_cayley_has_no_negative_one_eigenvector
    (skew : Matrix N N ℝ) (hskew : skewᵀ = -skew) (vector : N → ℝ)
    (heigen : actualCayley skew *ᵥ vector = -vector) : vector=0 := by
  have hzero : (actualCayley skew+1)*ᵥ vector=0 := by simp [Matrix.add_mulVec,heigen]
  have hinjective := Matrix.mulVec_injective_iff_isUnit.mpr
    (actual_cayley_plus_identity_is_invertible skew hskew)
  exact hinjective (by simpa using hzero)

end SafeLearning.CompleteModulesCayley
