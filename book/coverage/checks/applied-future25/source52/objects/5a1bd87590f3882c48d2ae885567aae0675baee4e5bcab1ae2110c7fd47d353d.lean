import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRNumbers

def actualDelayedKernel : ℝ := Real.sqrt 2/4
def actualCurrentKernel : ℝ := Real.sqrt 6/4
def actualSourceKernelRow : Matrix (Fin 1) (Fin 2) ℝ := !![actualDelayedKernel,actualCurrentKernel]
def actualSourceCholesky : Matrix (Fin 2) (Fin 2) ℝ := (1/Real.sqrt 2:ℝ) • 1

theorem actual_source_cholesky_is_exact_positive_factor :
    actualSourceCholeskyᵀ*actualSourceCholesky=(1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (∀ coordinate,0 < actualSourceCholesky coordinate coordinate) := by
  have hs : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [actualSourceCholesky,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals field_simp
    all_goals nlinarith
  · intro coordinate
    simp [actualSourceCholesky]


theorem actual_source_trigonometric_kernel_is_exact_radical :
    Real.cos (Real.pi/3)/Real.sqrt 2=actualDelayedKernel ∧
    Real.sin (Real.pi/3)/Real.sqrt 2=actualCurrentKernel := by
  have hs : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hm : Real.sqrt 6=Real.sqrt 2*Real.sqrt 3 := by
    calc
      Real.sqrt 6=Real.sqrt ((2:ℝ)*3) := by norm_num
      _=Real.sqrt 2*Real.sqrt 3 := Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num) (3:ℝ)
  rw [Real.cos_pi_div_three,Real.sin_pi_div_three]
  constructor
  · unfold actualDelayedKernel
    field_simp
    nlinarith
  · unfold actualCurrentKernel
    rw [hm]
    field_simp
    nlinarith

theorem actual_corrected_kernel_decimal_bounds :
    |actualDelayedKernel-(3536/10000:ℝ)| < 1/20000 ∧
    |actualCurrentKernel-(6124/10000:ℝ)| < 1/20000 ∧
    |(1/Real.sqrt 2:ℝ)-(7071/10000:ℝ)| < 1/20000 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hn2 := Real.sqrt_nonneg (2:ℝ)
  have hn6 := Real.sqrt_nonneg (6:ℝ)
  have hp2 := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  have hinv : 1/Real.sqrt 2=Real.sqrt 2/2 := by field_simp; nlinarith
  rw [hinv]
  simp only [actualDelayedKernel,actualCurrentKernel,abs_lt]
  constructor
  · constructor <;> nlinarith
  · constructor <;> constructor <;> nlinarith

def actualExactCertificate : Matrix (Fin 2) (Fin 2) ℝ :=
  (1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)-actualSourceKernelRowᵀ*actualSourceKernelRow

theorem actual_source_certificate_is_exact_radical_matrix :
    actualExactCertificate=!![3/8,-Real.sqrt 3/8;-Real.sqrt 3/8,1/8] := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hm : Real.sqrt 2*Real.sqrt 6=2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
    have hh := Real.sqrt_mul (show (0:ℝ) ≤ 4 by norm_num) (3:ℝ)
    norm_num at hh ⊢
    exact hh
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [actualExactCertificate,actualSourceKernelRow,actualDelayedKernel,actualCurrentKernel,
      Matrix.mul_apply,Fin.sum_univ_one]
  all_goals nlinarith

theorem actual_source_certificate_determinant_and_trace :
    actualExactCertificate.det=0 ∧ actualExactCertificate.trace=(1/2:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  rw [actual_source_certificate_is_exact_radical_matrix]
  constructor
  · rw [Matrix.det_fin_two]
    simp
    nlinarith
  · norm_num [Matrix.trace,Fin.sum_univ_two]

theorem actual_certificate_off_diagonal_decimal_bound :
    |(-Real.sqrt 3/8)-(-2165/10000:ℝ)| < 1/20000 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3:ℝ)
  rw [abs_lt]
  constructor <;> nlinarith

theorem actual_source_frequency_gain_value_and_rounding :
    |actualCurrentKernel|+|actualDelayedKernel|=(Real.sqrt 2+Real.sqrt 6)/4 ∧
    |((Real.sqrt 2+Real.sqrt 6)/4)-(9659/10000:ℝ)| < 1/20000 ∧
    (Real.sqrt 2+Real.sqrt 6)/4 < 1 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hn2 := Real.sqrt_nonneg (2:ℝ)
  have hn6 := Real.sqrt_nonneg (6:ℝ)
  constructor
  · rw [abs_of_nonneg (show 0 ≤ actualCurrentKernel by unfold actualCurrentKernel; positivity),
      abs_of_nonneg (show 0 ≤ actualDelayedKernel by unfold actualDelayedKernel; positivity)]
    unfold actualCurrentKernel actualDelayedKernel
    ring
  · constructor
    · rw [abs_lt]
      have hl2 : (141421/100000:ℝ) < Real.sqrt 2 := by nlinarith
      have hu2 : Real.sqrt 2 < (141422/100000:ℝ) := by nlinarith
      have hl6 : (244948/100000:ℝ) < Real.sqrt 6 := by nlinarith
      have hu6 : Real.sqrt 6 < (244950/100000:ℝ) := by nlinarith
      constructor <;> linarith
    · have hu2 : Real.sqrt 2 < (3/2:ℝ) := by nlinarith
      have hu6 : Real.sqrt 6 < (5/2:ℝ) := by nlinarith
      linarith

end SafeLearning.CompleteModulesFIRNumbers
