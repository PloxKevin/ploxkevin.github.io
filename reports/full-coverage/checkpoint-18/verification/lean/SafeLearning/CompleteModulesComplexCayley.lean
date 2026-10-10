import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped ComplexOrder
namespace SafeLearning.CompleteModulesComplexCayley

variable {N : Type*} [Fintype N] [DecidableEq N]

def actualComplexCayley (skew : Matrix N N ℂ) : Matrix N N ℂ :=
  (1-skew)*(1+skew)⁻¹

theorem actual_complex_skew_denominator_gram_is_positive
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) :
    ((1+skew)ᴴ*(1+skew)).PosDef := by
  have he : (1+skew)ᴴ*(1+skew)=(1 : Matrix N N ℂ)+skewᴴ*skew := by
    rw [Matrix.conjTranspose_add,Matrix.conjTranspose_one,hskew]
    noncomm_ring
  rw [he]
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self skew)

theorem actual_complex_skew_denominator_is_invertible
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) : IsUnit (1+skew) := by
  have hg := (actual_complex_skew_denominator_gram_is_positive skew hskew).isUnit
  have hd := (((1+skew)ᴴ*(1+skew)).isUnit_iff_isUnit_det.mp hg)
  rw [Matrix.det_mul] at hd
  apply (1+skew).isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  rw [hzero,mul_zero] at hd
  norm_num at hd

theorem actual_complex_skew_numerator_is_adjoint_denominator
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) : (1+skew)ᴴ=1-skew := by
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_one,hskew,sub_eq_add_neg]

theorem actual_complex_skew_numerator_is_invertible
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) : IsUnit (1-skew) := by
  rw [← actual_complex_skew_numerator_is_adjoint_denominator skew hskew,
    Matrix.isUnit_conjTranspose]
  exact actual_complex_skew_denominator_is_invertible skew hskew

theorem actual_complex_cayley_is_unitary
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) :
    (actualComplexCayley skew)ᴴ*actualComplexCayley skew=1 := by
  letI := (actual_complex_skew_denominator_is_invertible skew hskew).invertible
  letI := (actual_complex_skew_numerator_is_invertible skew hskew).invertible
  have hn : (1-skew)ᴴ=1+skew := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hskew,sub_neg_eq_add]
  have hc : (1+skew)*(1-skew)=(1-skew)*(1+skew) := by noncomm_ring
  unfold actualComplexCayley
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,
    actual_complex_skew_numerator_is_adjoint_denominator skew hskew,hn]
  calc
    _ = (1-skew)⁻¹*((1+skew)*(1-skew))*(1+skew)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1-skew)⁻¹*((1-skew)*(1+skew))*(1+skew)⁻¹ := by rw [hc]
    _ = 1 := by rw [← Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.one_mul,
      Matrix.mul_inv_of_invertible]

theorem actual_complex_cayley_determinant_has_unit_norm
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) :
    ‖(actualComplexCayley skew).det‖=1 := by
  have he := congrArg Matrix.det (actual_complex_cayley_is_unitary skew hskew)
  rw [Matrix.det_mul,Matrix.det_conjTranspose,Matrix.det_one] at he
  have hn := congrArg (fun value : ℂ => ‖value‖) he
  simp only [norm_mul,norm_star,norm_one] at hn
  nlinarith [norm_nonneg (actualComplexCayley skew).det]

theorem actual_complex_cayley_plus_identity_is_twice_inverse
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) :
    actualComplexCayley skew+1=(2:ℂ) • (1+skew)⁻¹ := by
  letI := (actual_complex_skew_denominator_is_invertible skew hskew).invertible
  unfold actualComplexCayley
  have he : (1 : Matrix N N ℂ)=(1+skew)*(1+skew)⁻¹ :=
    (Matrix.mul_inv_of_invertible (1+skew)).symm
  calc
    _ = (1-skew)*(1+skew)⁻¹+(1+skew)*(1+skew)⁻¹ := congrArg (_+·) he
    _ = ((1-skew)+(1+skew))*(1+skew)⁻¹ := by noncomm_ring
    _ = (2:ℂ) • (1+skew)⁻¹ := by
      have hsum : (1-skew)+(1+skew)=(2:ℂ) • (1 : Matrix N N ℂ) := by module
      rw [hsum,Matrix.smul_mul,Matrix.one_mul]

theorem actual_complex_cayley_plus_identity_is_invertible
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) : IsUnit (actualComplexCayley skew+1) := by
  rw [actual_complex_cayley_plus_identity_is_twice_inverse skew hskew]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_smul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  · exact Matrix.isUnit_nonsing_inv_det _
      ((1+skew).isUnit_iff_isUnit_det.mp (actual_complex_skew_denominator_is_invertible skew hskew))

theorem actual_complex_cayley_has_no_negative_one_eigenvector
    (skew : Matrix N N ℂ) (hskew : skewᴴ= -skew) (vector : N → ℂ)
    (heigen : actualComplexCayley skew*ᵥvector= -vector) : vector=0 := by
  have hz : (actualComplexCayley skew+1)*ᵥvector=0 := by simp [Matrix.add_mulVec,heigen]
  have hinjective := Matrix.mulVec_injective_iff_isUnit.mpr
    (actual_complex_cayley_plus_identity_is_invertible skew hskew)
  exact hinjective (by simpa using hz)

end SafeLearning.CompleteModulesComplexCayley
