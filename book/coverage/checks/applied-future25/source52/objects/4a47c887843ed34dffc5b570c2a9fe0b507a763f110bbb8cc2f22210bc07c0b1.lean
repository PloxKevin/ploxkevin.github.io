import SafeLearning.CompleteFoundationsMatrixNormModels
import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsPowerNormalization

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix norm_squared_coordinates matrix_coordinate_action)
open SafeLearning.CompleteFoundationsMatrixNormModels (diagonal_two_spectral_norm)

def matrixMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap
def frobeniusLength {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := Real.sqrt (∑ i,∑ j,A i j^2)

theorem actual_matrix_action_squared_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖matrixMap A x‖^2 ≤ (∑ i,∑ j,A i j^2)*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(∑ j,A i j*x j)^2) ≤ (∑ i,∑ j,A i j^2)*(∑ j,x j^2)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)

theorem actual_spectral_le_frobenius {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) : ‖A‖ ≤ frobeniusLength A := by
  rw [Matrix.l2_opNorm_def]
  change ‖matrixMap A‖ ≤ frobeniusLength A
  apply (matrixMap A).opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  have hs : (frobeniusLength A)^2=∑ i,∑ j,A i j^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _)))
  have hb : ‖matrixMap A x‖^2 ≤ (frobeniusLength A*‖x‖)^2 := by
    rw [mul_pow,hs]
    exact actual_matrix_action_squared_bound A x
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hb

section Frobenius
open scoped Matrix.Norms.Frobenius
theorem actual_frobenius_length_is_norm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : frobeniusLength A=‖A‖ := by
  symm
  simpa [frobeniusLength,Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow,one_div] using Matrix.frobenius_norm_def A
end Frobenius

theorem actual_unit_direction_estimate_is_lower_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) (hx : ‖x‖=1) :
    ‖matrixMap A x‖ ≤ ‖A‖ := by
  have hb := (matrixMap A).le_opNorm x
  rw [Matrix.l2_opNorm_def]
  change ‖matrixMap A x‖ ≤ ‖matrixMap A‖
  simpa [hx] using hb

theorem actual_upper_bound_normalizes {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) (c : ℝ) (hc : 0 < c) (hbound : ‖A‖ ≤ c) :
    ‖c⁻¹ • A‖ ≤ 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
  have h : ‖A‖/c ≤ 1 := (div_le_one hc).mpr hbound
  simpa [div_eq_mul_inv,mul_comm] using h

def sourceA : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![3,1]
def xZero : E := point (1/Real.sqrt 2) (1/Real.sqrt 2)
def estimateZero : ℝ := ‖applyMatrix sourceA xZero‖
def powerStep (x : E) : E := ‖applyMatrix (sourceAᵀ*sourceA) x‖⁻¹ • applyMatrix (sourceAᵀ*sourceA) x
def xOne : E := powerStep xZero
def estimateOne : ℝ := ‖applyMatrix sourceA xOne‖

theorem actual_source_spectral_norm : ‖sourceA‖=3 := by
  rw [sourceA,diagonal_two_spectral_norm]
  norm_num

theorem actual_source_gram : sourceAᵀ*sourceA=Matrix.diagonal ![9,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceA,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_x_zero_unit : ‖xZero‖=1 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (1/Real.sqrt 2 : ℝ)^2=1/2 := by rw [div_pow,one_pow,hs]
  have hn := norm_squared_coordinates xZero
  change ‖xZero‖^2=(1/Real.sqrt 2)^2+(1/Real.sqrt 2)^2 at hn
  nlinarith [norm_nonneg xZero]

theorem actual_initial_action : applyMatrix sourceA xZero=point (3/Real.sqrt 2) (1/Real.sqrt 2) := by
  rw [matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [sourceA,xZero,point,Matrix.diagonal] <;> ring

theorem actual_initial_estimate : estimateZero=Real.sqrt 5 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : estimateZero^2=5 := by
    rw [estimateZero,actual_initial_action,norm_squared_coordinates]
    change (3/Real.sqrt 2)^2+(1/Real.sqrt 2)^2=5
    rw [div_pow,div_pow,hs]
    norm_num
  have hroot : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hsq.trans hroot.symm)

theorem actual_gram_action :
    applyMatrix (sourceAᵀ*sourceA) xZero=point (9/Real.sqrt 2) (1/Real.sqrt 2) := by
  rw [actual_source_gram,matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [xZero,point,Matrix.diagonal] <;> ring

theorem actual_gram_action_norm : ‖applyMatrix (sourceAᵀ*sourceA) xZero‖=Real.sqrt 41 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : ‖applyMatrix (sourceAᵀ*sourceA) xZero‖^2=41 := by
    rw [actual_gram_action,norm_squared_coordinates]
    change (9/Real.sqrt 2)^2+(1/Real.sqrt 2)^2=41
    rw [div_pow,div_pow,hs]
    norm_num
  have hroot : (Real.sqrt 41)^2=41 := Real.sq_sqrt (by norm_num)
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hsq.trans hroot.symm)

theorem actual_power_iterate : xOne=point (9/Real.sqrt 82) (1/Real.sqrt 82) := by
  have hm : Real.sqrt 2*Real.sqrt 41=Real.sqrt 82 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [xOne,powerStep,actual_gram_action_norm,actual_gram_action]
  ext i
  fin_cases i <;> simp [point]
  · rw [← hm]
    field_simp
  · rw [← hm]
    field_simp

theorem actual_x_one_unit : ‖xOne‖=1 := by
  have hs : (Real.sqrt 82)^2=82 := Real.sq_sqrt (by norm_num)
  have hn := norm_squared_coordinates xOne
  rw [actual_power_iterate] at hn
  change ‖point (9/Real.sqrt 82) (1/Real.sqrt 82)‖^2=(9/Real.sqrt 82)^2+(1/Real.sqrt 82)^2 at hn
  rw [div_pow,div_pow,hs] at hn
  have hh : ‖xOne‖^2=1 := by rw [actual_power_iterate];norm_num at hn ⊢;exact hn
  nlinarith [norm_nonneg xOne]

theorem actual_next_action : applyMatrix sourceA xOne=point (27/Real.sqrt 82) (1/Real.sqrt 82) := by
  rw [actual_power_iterate,matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [sourceA,point,Matrix.diagonal] <;> ring

theorem actual_next_estimate : estimateOne=Real.sqrt (730/82) := by
  have hs : (Real.sqrt 82)^2=82 := Real.sq_sqrt (by norm_num)
  have hsq : estimateOne^2=730/82 := by
    rw [estimateOne,actual_next_action,norm_squared_coordinates]
    change (27/Real.sqrt 82)^2+(1/Real.sqrt 82)^2=730/82
    rw [div_pow,div_pow,hs]
    norm_num
  have hroot : (Real.sqrt (730/82))^2=730/82 := Real.sq_sqrt (by norm_num)
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hsq.trans hroot.symm)

theorem actual_improvement_below_true_norm : 0 < estimateZero ∧ estimateZero < estimateOne ∧ estimateOne < ‖sourceA‖ := by
  rw [actual_initial_estimate,actual_next_estimate,actual_source_spectral_norm]
  have h0 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 730/82)
  constructor
  · exact Real.sqrt_pos.mpr (by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg 5,Real.sqrt_nonneg (730/82)]

theorem actual_failed_normalization : ‖estimateZero⁻¹ • sourceA‖=3/Real.sqrt 5 ∧ 1 < ‖estimateZero⁻¹ • sourceA‖ := by
  have hr : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [actual_initial_estimate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),actual_source_spectral_norm]
  constructor
  · ring
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hlt : Real.sqrt 5 < 3 := by nlinarith
    exact (one_lt_div hr).mpr hlt |>.trans_eq (by ring)

theorem actual_source_frobenius : frobeniusLength sourceA=Real.sqrt 10 := by
  norm_num [frobeniusLength,sourceA,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_guaranteed_normalizations :
    ‖(1/3 : ℝ) • sourceA‖=1 ∧ ‖(frobeniusLength sourceA)⁻¹ • sourceA‖ ≤ 1 := by
  constructor
  · rw [norm_smul,Real.norm_eq_abs,actual_source_spectral_norm]
    norm_num
  · exact actual_upper_bound_normalizes sourceA (frobeniusLength sourceA)
      (by rw [actual_source_frobenius];positivity) (actual_spectral_le_frobenius sourceA)

theorem actual_printed_decimal_enclosures :
    |estimateZero-2.2361| < 0.00005 ∧ |estimateOne-2.9837| < 0.00005 ∧
    |‖estimateZero⁻¹ • sourceA‖-1.3416| < 0.00005 := by
  rw [actual_failed_normalization.1,actual_initial_estimate,actual_next_estimate]
  have hs0 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 730/82)
  have hr0 := Real.sqrt_nonneg 5
  have hr1 := Real.sqrt_nonneg (730/82)
  have hlo : (2.23605 : ℝ) < Real.sqrt 5 := by nlinarith
  have hhi : Real.sqrt 5 < (2.23615 : ℝ) := by nlinarith
  have hdlo : (1.34155 : ℝ) < 3/Real.sqrt 5 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    nlinarith
  have hdhi : 3/Real.sqrt 5 < (1.34165 : ℝ) := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · rw [abs_lt]
    constructor <;> linarith

end SafeLearning.CompleteFoundationsPowerNormalization
