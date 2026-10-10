import SafeLearning.CompleteModulesThreeTapConvolution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesThreeTapTransfer
open CompleteModulesThreeTapConvolution
variable {I O R : Type*} [Fintype I] [Fintype O] [DecidableEq I] [Field R]

theorem actual_three_tap_resolvent_inverse_formula (z : R) (hz : z≠0) :
    (z • (1 : Matrix (Sum I I) (Sum I I) R)-actualThreeTapStateMatrix)⁻¹=
      z⁻¹ • (1 : Matrix (Sum I I) (Sum I I) R)+(z⁻¹)^2 • actualThreeTapStateMatrix := by
  apply Matrix.inv_eq_right_inv
  have hzero : (actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R)*actualThreeTapStateMatrix=0 :=
    by simpa only [pow_two] using (actual_three_tap_state_matrix_squared_is_zero (I:=I) (R:=R))
  have hcoefficient : z*(z⁻¹)^2=z⁻¹ := by field_simp [hz]
  simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,hzero,smul_zero]
  simp only [smul_sub,smul_smul,sub_zero]
  rw [inv_mul_cancel₀ hz,show (z⁻¹)^2*z=z⁻¹ by rw [mul_comm];exact hcoefficient]
  simp

theorem actual_three_tap_current_delay_matrix_product (delayed twiceDelayed : Matrix O I R) :
    actualThreeTapOutputMatrix delayed twiceDelayed*(actualThreeTapInputMatrix : Matrix (Sum I I) I R)=delayed := by
  simp [actualThreeTapOutputMatrix,actualThreeTapInputMatrix,Matrix.fromCols_mul_fromRows]

theorem actual_three_tap_second_delay_matrix_product (delayed twiceDelayed : Matrix O I R) :
    actualThreeTapOutputMatrix delayed twiceDelayed*
      (actualThreeTapStateMatrix : Matrix (Sum I I) (Sum I I) R)*actualThreeTapInputMatrix=twiceDelayed := by
  unfold actualThreeTapOutputMatrix actualThreeTapStateMatrix actualThreeTapInputMatrix
  rw [Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows]
  simp

theorem actual_three_tap_state_space_transfer_equals_kernel_polynomial
    (current delayed twiceDelayed : Matrix O I R) (z : R) (hz : z≠0) :
    actualThreeTapOutputMatrix delayed twiceDelayed*
      (z • (1 : Matrix (Sum I I) (Sum I I) R)-actualThreeTapStateMatrix)⁻¹*
      actualThreeTapInputMatrix+current=
    current+z⁻¹ • delayed+(z⁻¹)^2 • twiceDelayed := by
  rw [actual_three_tap_resolvent_inverse_formula z hz]
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,Matrix.smul_mul]
  rw [actual_three_tap_current_delay_matrix_product,actual_three_tap_second_delay_matrix_product]
  abel

theorem actual_three_tap_state_and_layer_lmi_index_dimensions :
    Fintype.card (Sum I I)=2*Fintype.card I ∧
    Fintype.card (Sum (Sum (Sum I I) I) O)=3*Fintype.card I+Fintype.card O := by
  simp only [Fintype.card_sum]
  constructor <;> omega

end SafeLearning.CompleteModulesThreeTapTransfer
