import SafeLearning.CompleteAppliedCoordinateTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCoordinateTransferConsequences
open SafeLearning.CompleteAppliedCoordinateTransfer

theorem actual_source_diagonal_coordinate_transform_commutes_with_the_dynamics :
    T*A=A*T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T,A,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_transformed_transfer_has_the_literal_changed_input_and_output_factors
    (s : ℂ) (h1 : s+1≠0) (h2 : s+2≠0) :
    transformedTransfer s=(1/2:ℂ)*2/(s+1)+1*1/(s+2) := by
  rw [(actual_transformed_transfer_is_the_same_rational_map s h1 h2).1]
  ring

end SafeLearning.CompleteAppliedCoordinateTransferConsequences
