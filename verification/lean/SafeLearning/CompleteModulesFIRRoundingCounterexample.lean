import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesFIRRoundingCounterexample

def actualPrintedRoundedCertificate : Matrix (Fin 2) (Fin 2) ℝ :=
  !![375/1000,-2165/10000;-2165/10000,125/1000]

theorem actual_printed_rounded_certificate_determinant :
    actualPrintedRoundedCertificate.det=(11/4000000:ℝ) := by
  rw [Matrix.det_fin_two]
  norm_num [actualPrintedRoundedCertificate]

theorem actual_printed_rounded_certificate_determinant_is_not_zero :
    actualPrintedRoundedCertificate.det≠0 := by
  rw [actual_printed_rounded_certificate_determinant]
  norm_num

theorem actual_printed_cholesky_decimal_is_not_exact :
    (7071/10000:ℝ)^2≠1/2 := by norm_num

theorem actual_printed_rounded_kernel_gain :
    (3536/10000:ℝ)+(6124/10000:ℝ)=966/1000 := by norm_num

theorem actual_printed_rounded_kernel_gain_is_not_quoted_decimal :
    (3536/10000:ℝ)+(6124/10000:ℝ)≠9659/10000 := by norm_num

end SafeLearning.CompleteModulesFIRRoundingCounterexample
