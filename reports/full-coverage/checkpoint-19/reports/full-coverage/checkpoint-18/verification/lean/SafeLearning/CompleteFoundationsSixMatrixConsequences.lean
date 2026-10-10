import SafeLearning.CompleteFoundationsSixMatrixSpectral
import SafeLearning.CompleteFoundationsSixMatrixComplex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped ENNReal Matrix.Norms.Operator
namespace SafeLearning.CompleteFoundationsSixMatrixConsequences
open CompleteFoundationsSixMatrixNorms CompleteFoundationsSixMatrixSpectral
open CompleteFoundationsSixMatrixComplex

theorem actual_source_closed_complex_root_formulas :
    eigenPlus=((5:ℂ)+(Real.sqrt 15:ℂ)*Complex.I)/2 ∧
    eigenMinus=((5:ℂ)-(Real.sqrt 15:ℂ)*Complex.I)/2 := by
  constructor <;> apply Complex.ext <;> norm_num [eigenPlus,eigenMinus,Complex.div_re,Complex.div_im]

theorem actual_standard_spectral_radius_below_source_euclidean_norm :
    (spectralRadius ℂ complexB).toReal≤‖twoMap‖ := by
  rw [actual_standard_complex_spectral_radius.2]
  exact actual_spectral_norm_below_frobenius_and_row_column_bound.2.2

theorem actual_spectral_norm_below_minimum_frobenius_and_true_column_row_product :
    ‖twoMap‖ ≤ min (Real.sqrt 30) (Real.sqrt (‖oneMap‖*‖sourceB‖)) := by
  rw [actual_one_map_spectral_one_norm,actual_matrix_infinity_norm]
  exact le_min actual_spectral_norm_below_frobenius_and_row_column_bound.1
    actual_spectral_norm_below_frobenius_and_row_column_bound.2.1

end SafeLearning.CompleteFoundationsSixMatrixConsequences
