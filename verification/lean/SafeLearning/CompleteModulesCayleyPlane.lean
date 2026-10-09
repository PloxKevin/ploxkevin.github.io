import SafeLearning.CompleteModulesCayley
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesCayleyPlane

def actualPlaneSkew (parameter : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0,parameter;-parameter,0]

def actualPlaneRotation (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos angle,-Real.sin angle;Real.sin angle,Real.cos angle]

theorem actual_plane_matrix_is_skew (parameter : ℝ) :
    (actualPlaneSkew parameter)ᵀ= -actualPlaneSkew parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [actualPlaneSkew,Matrix.transpose_apply]

theorem actual_plane_denominator_inverse (parameter : ℝ) :
    (1+actualPlaneSkew parameter)⁻¹=
      (1/(1+parameter^2)) • (!![1,-parameter;parameter,1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.inv_eq_right_inv
  have hpositive : 0<1+parameter^2 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualPlaneSkew,Matrix.mul_apply,Fin.sum_univ_two,Matrix.add_apply,
      Matrix.smul_apply,Matrix.one_apply] <;> field_simp <;> ring

theorem actual_plane_cayley_formula (parameter : ℝ) :
    SafeLearning.CompleteModulesCayley.actualCayley (actualPlaneSkew parameter)=
      (1/(1+parameter^2)) •
        (!![1-parameter^2,-2*parameter;2*parameter,1-parameter^2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold SafeLearning.CompleteModulesCayley.actualCayley
  rw [actual_plane_denominator_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualPlaneSkew,Matrix.mul_apply,Fin.sum_univ_two,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.one_apply] <;> ring

theorem actual_arctan_rotation_coordinates (parameter : ℝ) :
    Real.cos (2*Real.arctan parameter)=(1-parameter^2)/(1+parameter^2) ∧
      Real.sin (2*Real.arctan parameter)=2*parameter/(1+parameter^2) := by
  have hpositive : 0<1+parameter^2 := by positivity
  have hsqrt : Real.sqrt (1+parameter^2) ≠ 0 := (Real.sqrt_pos.2 hpositive).ne'
  have hsquare := Real.sq_sqrt hpositive.le
  constructor
  · rw [Real.cos_two_mul,Real.cos_arctan]
    field_simp
    nlinarith
  · rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
    field_simp
    nlinarith [congrArg (fun value : ℝ => parameter*value) hsquare]

theorem actual_plane_cayley_is_rotation (parameter : ℝ) :
    SafeLearning.CompleteModulesCayley.actualCayley (actualPlaneSkew parameter)=
      actualPlaneRotation (2*Real.arctan parameter) := by
  rw [actual_plane_cayley_formula]
  obtain ⟨hcos,hsin⟩ := actual_arctan_rotation_coordinates parameter
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualPlaneRotation,Matrix.smul_apply,hcos,hsin] <;> ring

theorem actual_plane_cayley_angle_is_in_open_pi_interval (parameter : ℝ) :
    -Real.pi<2*Real.arctan parameter ∧ 2*Real.arctan parameter<Real.pi := by
  constructor
  · have h := Real.neg_pi_div_two_lt_arctan parameter
    linarith
  · have h := Real.arctan_lt_pi_div_two parameter
    linarith

theorem actual_half_parameter_cayley_matrix :
    SafeLearning.CompleteModulesCayley.actualCayley (actualPlaneSkew (1/2))=
      (!![(3/5:ℝ),-4/5;4/5,3/5] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [actual_plane_cayley_formula]
  norm_num

theorem actual_plane_cayley_never_produces_reflection
    (parameter : ℝ) (reflection : Matrix (Fin 2) (Fin 2) ℝ)
    (hreflection : reflection.det= -1) :
    SafeLearning.CompleteModulesCayley.actualCayley (actualPlaneSkew parameter)≠reflection := by
  intro he
  have hd := SafeLearning.CompleteModulesCayley.actual_cayley_has_determinant_one
    (actualPlaneSkew parameter) (actual_plane_matrix_is_skew parameter)
  rw [he,hreflection] at hd
  norm_num at hd

theorem actual_plane_cayley_never_produces_pi_rotation (parameter : ℝ) :
    SafeLearning.CompleteModulesCayley.actualCayley (actualPlaneSkew parameter)≠
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro he
  have hunit := SafeLearning.CompleteModulesCayley.actual_cayley_plus_identity_is_invertible
    (actualPlaneSkew parameter) (actual_plane_matrix_is_skew parameter)
  rw [he,neg_add_cancel] at hunit
  have hd := ((0 : Matrix (Fin 2) (Fin 2) ℝ).isUnit_iff_isUnit_det.mp hunit)
  norm_num at hd

def actualHalfArctanTerm (index : ℕ) : ℝ :=
  (1/2:ℝ)^(2*index+1)/((2*index+1:ℕ):ℝ)

theorem actual_half_arctan_terms_are_antitone : Antitone actualHalfArctanTerm := by
  apply antitone_nat_of_succ_le
  intro index
  unfold actualHalfArctanTerm
  apply div_le_div₀ (by positivity)
  · apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  · positivity
  · exact_mod_cast (show 2*index+1≤2*(index+1)+1 by omega)

theorem actual_half_parameter_angle_rounds_to_53_13_degrees :
    |(2*Real.arctan (1/2))*180/Real.pi-(5313/100:ℝ)|≤1/200 := by
  have hseries := Real.hasSum_arctan (x := (1/2:ℝ)) (by norm_num)
  have hlimit : Filter.Tendsto
      (fun count : ℕ => ∑ index ∈ Finset.range count, (-1:ℝ)^index*actualHalfArctanTerm index)
      Filter.atTop (nhds (Real.arctan (1/2))) := by
    simpa [actualHalfArctanTerm,mul_div_assoc] using hseries.tendsto_sum_nat
  have hl := actual_half_arctan_terms_are_antitone.alternating_series_le_tendsto hlimit 5
  have hu := actual_half_arctan_terms_are_antitone.tendsto_le_alternating_series hlimit 5
  norm_num [Finset.sum_range_succ,actualHalfArctanTerm] at hl hu
  have hlow : (53125/1000:ℝ)<(2*Real.arctan (1/2))*180/Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d6]
  have hhigh : (2*Real.arctan (1/2))*180/Real.pi<(53135/1000:ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d6]
  rw [abs_le]
  constructor <;> linarith

end SafeLearning.CompleteModulesCayleyPlane
