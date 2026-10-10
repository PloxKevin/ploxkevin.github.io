import SafeLearning.CompleteModulesLipSDP
import SafeLearning.CompleteModulesScaledGram

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSLL

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M]

def actualSLL (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (activation : ℝ → ℝ) (bias : N → ℝ) (input : M → ℝ) : M → ℝ :=
  input-(2:ℝ) • (weights*ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥ
    (fun coordinate => activation ((weightsᵀ*ᵥinput) coordinate+bias coordinate))))

theorem actual_positive_diagonal_inverse
    (diagonal : N → ℝ) (hpositive : ∀ coordinate, 0<diagonal coordinate) :
    (Matrix.diagonal diagonal)⁻¹=Matrix.diagonal (fun coordinate => (diagonal coordinate)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  ext row column
  rw [Matrix.diagonal_mul]
  by_cases he : row=column
  · subst column
    simp [Matrix.diagonal_apply,Matrix.one_apply,(hpositive row).ne']
  · simp [Matrix.diagonal_apply,Matrix.one_apply,he]

theorem actual_positive_diagonal_is_invertible
    (diagonal : N → ℝ) (hpositive : ∀ coordinate, 0<diagonal coordinate) :
    IsUnit (Matrix.diagonal diagonal) := by
  apply (Matrix.diagonal diagonal).isUnit_iff_isUnit_det.mpr
  rw [Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro coordinate hcoordinate
  exact (hpositive coordinate).ne'

theorem actual_residual_step_energy_identity
    (input direction : M → ℝ) :
    ‖WithLp.toLp 2 input‖^2-‖WithLp.toLp 2 (input-(2:ℝ) • direction)‖^2=
      4*(input ⬝ᵥdirection-direction ⬝ᵥdirection) := by
  rw [SafeLearning.CompleteModulesLipSDP.squared_norm_of_coordinates,
    SafeLearning.CompleteModulesLipSDP.squared_norm_of_coordinates]
  have hcoordinate : ∀ coordinate,
      (input coordinate-2*direction coordinate)^2=
        input coordinate^2-4*(input coordinate*direction coordinate)+4*(direction coordinate)^2 := by
    intro coordinate
    ring
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hcoordinate,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum,dotProduct,pow_two]
  ring_nf
  simp only [Finset.sum_mul]

theorem actual_sll_energy_gap_is_qc_plus_certificate
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate, 0<diagonal coordinate)
    (input : M → ℝ) (hidden : N → ℝ) :
    let inverse := (Matrix.diagonal diagonal)⁻¹
    let direction := inverse*ᵥhidden
    ‖WithLp.toLp 2 input‖^2-
      ‖WithLp.toLp 2 (input-(2:ℝ) • (weights*ᵥdirection))‖^2=
      4*(hidden ⬝ᵥ(inverse*ᵥ(weightsᵀ*ᵥinput-hidden)))+
      4*(direction ⬝ᵥ((Matrix.diagonal diagonal-weightsᵀ*weights)*ᵥdirection)) := by
  dsimp only
  let inverse := (Matrix.diagonal diagonal)⁻¹
  let direction := inverse*ᵥhidden
  have hisymmetric : inverseᵀ=inverse := by
    simp [inverse,actual_positive_diagonal_inverse diagonal hpositive]
  have hcross : input ⬝ᵥ(weights*ᵥdirection)=direction ⬝ᵥ(weightsᵀ*ᵥinput) := by
    rw [Matrix.dotProduct_transpose_mulVec,dotProduct_comm]
  have hgram : (weights*ᵥdirection) ⬝ᵥ(weights*ᵥdirection)=
      direction ⬝ᵥ((weightsᵀ*weights)*ᵥdirection) := by
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  have htranspose : direction ⬝ᵥ(weightsᵀ*ᵥinput)=
      hidden ⬝ᵥ(inverse*ᵥ(weightsᵀ*ᵥinput)) := by
    change (inverse*ᵥhidden) ⬝ᵥ(weightsᵀ*ᵥinput)=_
    conv_rhs => rw [← hisymmetric,Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  have hrecover : Matrix.diagonal diagonal*ᵥdirection=hidden := by
    letI := (actual_positive_diagonal_is_invertible diagonal hpositive).invertible
    dsimp [direction,inverse]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hdiagonal : direction ⬝ᵥ(Matrix.diagonal diagonal*ᵥdirection)=
      hidden ⬝ᵥ(inverse*ᵥhidden) := by
    rw [hrecover,dotProduct_comm]
  change ‖WithLp.toLp 2 input‖^2-
      ‖WithLp.toLp 2 (input-(2:ℝ) • (weights*ᵥdirection))‖^2=_
  rw [actual_residual_step_energy_identity,hcross,hgram]
  simp only [Matrix.sub_mulVec,Matrix.mulVec_sub,dotProduct_sub]
  rw [htranspose,hdiagonal]
  ring

theorem actual_sll_incremental_quadratic_constraint
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate, 0<diagonal coordinate)
    (activation : ℝ → ℝ)
    (hactivation : SafeLearning.CompleteModulesLipSDP.slopeRestricted activation 0 1)
    (bias : N → ℝ) (first second : M → ℝ) :
    let hidden := fun coordinate =>
      activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
        activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)
    0≤hidden ⬝ᵥ((Matrix.diagonal diagonal)⁻¹*ᵥ(weightsᵀ*ᵥ(first-second)-hidden)) := by
  dsimp only
  rw [actual_positive_diagonal_inverse diagonal hpositive]
  simp only [Matrix.mulVec_diagonal,dotProduct,Pi.mul_apply,Pi.sub_apply]
  apply Finset.sum_nonneg
  intro coordinate hcoordinate
  have hq := SafeLearning.CompleteModulesLipSDP.scalar_slope_quadratic_constraint
    activation 0 1 hactivation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)
      ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)
  simp only [zero_mul,mul_zero,zero_add,add_zero,one_mul,add_sub_add_right_eq_sub,
    Matrix.mulVec_sub,Pi.sub_apply] at hq ⊢
  have hscalar : 0≤(activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
      activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate))*
        (((weightsᵀ*ᵥfirst) coordinate-(weightsᵀ*ᵥsecond) coordinate)-
          (activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
            activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate))) := by
    nlinarith
  have hinverse := inv_nonneg.mpr (hpositive coordinate).le
  nlinarith [mul_nonneg hinverse hscalar]

theorem actual_sll_is_euclidean_nonexpansive
    (weights : Matrix M N ℝ) (diagonal : N → ℝ)
    (hpositive : ∀ coordinate, 0<diagonal coordinate)
    (hcertificate : (Matrix.diagonal diagonal-weightsᵀ*weights).PosSemidef)
    (activation : ℝ → ℝ)
    (hactivation : SafeLearning.CompleteModulesLipSDP.slopeRestricted activation 0 1)
    (bias : N → ℝ) (first second : M → ℝ) :
    ‖WithLp.toLp 2 (actualSLL weights diagonal activation bias first-
      actualSLL weights diagonal activation bias second)‖≤‖WithLp.toLp 2 (first-second)‖ := by
  let hidden := fun coordinate =>
    activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
      activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)
  let direction := (Matrix.diagonal diagonal)⁻¹*ᵥhidden
  have houtput : actualSLL weights diagonal activation bias first-
      actualSLL weights diagonal activation bias second=
      (first-second)-(2:ℝ) • (weights*ᵥdirection) := by
    unfold actualSLL
    dsimp [direction,hidden]
    have hh : (fun coordinate => activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate)-
        activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate))=
        (fun coordinate => activation ((weightsᵀ*ᵥfirst) coordinate+bias coordinate))-
          (fun coordinate => activation ((weightsᵀ*ᵥsecond) coordinate+bias coordinate)) := rfl
    rw [hh,Matrix.mulVec_sub,Matrix.mulVec_sub]
    module
  have he := actual_sll_energy_gap_is_qc_plus_certificate weights diagonal hpositive
    (first-second) hidden
  have hq := actual_sll_incremental_quadratic_constraint weights diagonal hpositive
    activation hactivation bias first second
  have hr := hcertificate.dotProduct_mulVec_nonneg direction
  simp only [star_trivial] at hr
  rw [houtput]
  dsimp only at he hq
  nlinarith [norm_nonneg (WithLp.toLp 2 (first-second)),
    norm_nonneg (WithLp.toLp 2 ((first-second)-(2:ℝ) • (weights*ᵥdirection)))]

end SafeLearning.CompleteModulesSLL
