import SafeLearning.CompleteModulesDiagonalQC

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSectorExamples

open CompleteModulesLipSDP CompleteModulesDiagonalQC

def nonmonotoneSectorActivation (value : ℝ) : ℝ := value/(1+value^2)

theorem actual_nonmonotone_sector_formula (value : ℝ) :
    scalarQC 0 1 value (nonmonotoneSectorActivation value)=2*value^4/(1+value^2)^2 := by
  have hd : (1+value^2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg value]
  unfold scalarQC nonmonotoneSectorActivation
  field_simp
  ring

theorem actual_nonmonotone_function_obeys_sector :
    nonmonotoneSectorActivation 0=0 ∧
      ∀ value : ℝ, 0 ≤ scalarQC 0 1 value (nonmonotoneSectorActivation value) := by
  constructor
  · norm_num [nonmonotoneSectorActivation]
  · intro value
    rw [actual_nonmonotone_sector_formula]
    positivity

theorem sector_bounded_function_need_not_be_monotone :
    ¬ Monotone nonmonotoneSectorActivation := by
  intro h
  have hh := h (show (1:ℝ) ≤ 2 by norm_num)
  norm_num [nonmonotoneSectorActivation] at hh

theorem sector_bounded_function_need_not_be_slope_restricted :
    ¬ slopeRestricted nonmonotoneSectorActivation 0 1 := by
  intro h
  obtain ⟨slope,hl,hu,he⟩ := h 2 1
  norm_num [nonmonotoneSectorActivation] at he
  linarith

def maxMin (input : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![max (input 0) (input 1),min (input 0) (input 1)]

theorem actual_maxmin_violates_elementwise_diagonal_qc :
    diagonalQC 0 1 (![1,0] : Fin 2 → ℝ) (![0,1]-![0,0])
      (maxMin ![0,1]-maxMin ![0,0]) = -2 := by
  norm_num [diagonalQC,scalarQC,maxMin,Fin.sum_univ_two]

theorem maxmin_preserves_sum (input : Fin 2 → ℝ) :
    (maxMin input) 0+(maxMin input) 1=input 0+input 1 := by
  simp [maxMin,max_add_min]

theorem maxmin_preserves_squared_norm (input : Fin 2 → ℝ) :
    ‖WithLp.toLp 2 (maxMin input)‖^2=‖WithLp.toLp 2 input‖^2 := by
  simp only [squared_norm_of_coordinates,Fin.sum_univ_two]
  unfold maxMin
  by_cases h : input 0 ≤ input 1
  · simp [max_eq_right h,min_eq_left h,add_comm]
  · simp [max_eq_left (le_of_not_ge h),min_eq_right (le_of_not_ge h)]

theorem maxmin_is_euclidean_nonexpansive (first second : Fin 2 → ℝ) :
    ‖WithLp.toLp 2 (maxMin first-maxMin second)‖ ≤
      ‖WithLp.toLp 2 (first-second)‖ := by
  have hs : ‖WithLp.toLp 2 (maxMin first-maxMin second)‖^2 ≤
      ‖WithLp.toLp 2 (first-second)‖^2 := by
    simp only [squared_norm_of_coordinates,Fin.sum_univ_two,Pi.sub_apply]
    unfold maxMin
    by_cases hf : first 0 ≤ first 1 <;> by_cases hs : second 0 ≤ second 1
    · simp [max_eq_right hf,min_eq_left hf,max_eq_right hs,min_eq_left hs,add_comm]
    · simp [max_eq_right hf,min_eq_left hf,max_eq_left (le_of_not_ge hs),
        min_eq_right (le_of_not_ge hs)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr (le_of_not_ge hs))]
    · simp [max_eq_left (le_of_not_ge hf),min_eq_right (le_of_not_ge hf),
        max_eq_right hs,min_eq_left hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hf)) (sub_nonneg.mpr hs)]
    · simp [max_eq_left (le_of_not_ge hf),min_eq_right (le_of_not_ge hf),
        max_eq_left (le_of_not_ge hs),min_eq_right (le_of_not_ge hs)]
  nlinarith [norm_nonneg (WithLp.toLp 2 (maxMin first-maxMin second)),
    norm_nonneg (WithLp.toLp 2 (first-second))]

end SafeLearning.CompleteModulesSectorExamples
