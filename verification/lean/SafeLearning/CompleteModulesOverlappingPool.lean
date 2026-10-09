import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesOverlappingPool
open CompleteModulesLipSDP CompleteModulesLipSDPProduct

def actualAdjacentPairAveragePool : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1/2,1/2,0;0,1/2,1/2]

theorem actual_adjacent_pair_average_output (input : Fin 3 → ℝ) :
    actualAdjacentPairAveragePool*ᵥinput=
      ![(input 0+input 1)/2,(input 1+input 2)/2] := by
  ext coordinate
  fin_cases coordinate <;> simp [actualAdjacentPairAveragePool,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem actual_adjacent_pair_average_pool_quadratic_gap (first middle last : ℝ) :
    (3/4:ℝ)*(first^2+middle^2+last^2)-
      (((first+middle)/2)^2+((middle+last)/2)^2)=
        ((first-last)^2+(first-middle+last)^2)/4 := by ring

theorem actual_adjacent_pair_average_pool_spectral_norm_squared :
    ‖actualAdjacentPairAveragePool‖^2=(3/4:ℝ) := by
  have hupper : ‖actualAdjacentPairAveragePool‖ ≤ Real.sqrt (3/4:ℝ) := by
    apply CompleteModulesLipSDPWalkthrough.actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
    intro input
    rw [actual_adjacent_pair_average_output]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
    simp only [← add_assoc]
    change ((input 0+input 1)/2)^2+((input 1+input 2)/2)^2 ≤
      (3/4:ℝ)*(input 0^2+input 1^2+input 2^2)
    have hg := actual_adjacent_pair_average_pool_quadratic_gap (input 0) (input 1) (input 2)
    have hn : 0 ≤ ((input 0-input 2)^2+(input 0-input 1+input 2)^2)/4 := by positivity
    linarith
  let input : Fin 3 → ℝ := ![1,2,1]
  have hgain := actual_spectral_matrix_gain actualAdjacentPairAveragePool input
  have hin : ‖WithLp.toLp 2 input‖^2=(6:ℝ) := by
    rw [squared_norm_of_coordinates]
    norm_num [input,Fin.sum_univ_succ]
  have hout : ‖WithLp.toLp 2 (actualAdjacentPairAveragePool*ᵥinput)‖^2=(9/2:ℝ) := by
    rw [squared_norm_of_coordinates,actual_adjacent_pair_average_output]
    norm_num [input,Fin.sum_univ_succ]
  have hsquared : ‖WithLp.toLp 2 (actualAdjacentPairAveragePool*ᵥinput)‖^2 ≤
      ‖actualAdjacentPairAveragePool‖^2*‖WithLp.toLp 2 input‖^2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (actualAdjacentPairAveragePool*ᵥinput)),
      mul_nonneg (norm_nonneg actualAdjacentPairAveragePool) (norm_nonneg (WithLp.toLp 2 input))]
  rw [hin,hout] at hsquared
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3/4 by norm_num)
  nlinarith [Real.sqrt_nonneg (3/4:ℝ),norm_nonneg actualAdjacentPairAveragePool]

theorem actual_adjacent_pair_average_pool_spectral_norm :
    ‖actualAdjacentPairAveragePool‖=Real.sqrt 3/2 := by
  have he := actual_adjacent_pair_average_pool_spectral_norm_squared
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg (3:ℝ),norm_nonneg actualAdjacentPairAveragePool]

theorem actual_overlap_increases_the_disjoint_two_coordinate_bound :
    1/Real.sqrt 2 < ‖actualAdjacentPairAveragePool‖ := by
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have he := actual_adjacent_pair_average_pool_spectral_norm_squared
  have hi : (1/Real.sqrt (2:ℝ))^2=(1/2:ℝ) := by rw [div_pow,one_pow,hs]
  nlinarith [norm_nonneg actualAdjacentPairAveragePool,(show 0 < 1/Real.sqrt (2:ℝ) by positivity)]

end SafeLearning.CompleteModulesOverlappingPool
