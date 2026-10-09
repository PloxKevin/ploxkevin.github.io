import SafeLearning.CompleteModulesSLLExamples
import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesSLLSpectral
open CompleteModulesSLLExamples CompleteModulesLipSDP CompleteModulesLipSDPProduct

def actualGoldenRatio : ℝ := (1+Real.sqrt 5)/2

theorem actual_golden_ratio_identities :
    0 < actualGoldenRatio ∧ actualGoldenRatio^2=actualGoldenRatio+1 ∧
      (3+Real.sqrt 5)/2=actualGoldenRatio+1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  unfold actualGoldenRatio
  constructor
  · positivity
  · constructor
    · nlinarith
    · ring

theorem actual_source_weights_coordinate_energy (input : Fin 2 → ℝ) :
    (∑ row,((actualSourceWeights*ᵥinput) row)^2)=
      (input 0+input 1)^2+(input 1)^2 := by
  simp [actualSourceWeights,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_spectral_quadratic_gap (first second : ℝ) :
    ((3+Real.sqrt 5)/2)*(first^2+second^2)-((first+second)^2+second^2)=
      (actualGoldenRatio*first-second)^2/actualGoldenRatio := by
  obtain ⟨hp,he,hr⟩ := actual_golden_ratio_identities
  rw [hr]
  apply (eq_div_iff hp.ne').mpr
  nlinarith [sq_nonneg (actualGoldenRatio*first-second)]

theorem actual_source_spectral_norm_squared :
    ‖actualSourceWeights‖^2=(3+Real.sqrt 5)/2 := by
  obtain ⟨hp,he,hr⟩ := actual_golden_ratio_identities
  have hupper : ‖actualSourceWeights‖ ≤ Real.sqrt ((3+Real.sqrt 5)/2) := by
    apply CompleteModulesLipSDPWalkthrough.actual_spectral_norm_le_of_quadratic_bound _ _
      (by positivity)
    intro input
    rw [actual_source_weights_coordinate_energy]
    simp only [Fin.sum_univ_two]
    have hg := actual_source_spectral_quadratic_gap (input 0) (input 1)
    have hn : 0 ≤ (actualGoldenRatio*input 0-input 1)^2/actualGoldenRatio := by positivity
    linarith
  let input : Fin 2 → ℝ := ![1,actualGoldenRatio]
  have hgain := actual_spectral_matrix_gain actualSourceWeights input
  have hin : ‖WithLp.toLp 2 input‖^2=1+actualGoldenRatio^2 := by
    rw [squared_norm_of_coordinates]
    norm_num [input,Fin.sum_univ_two]
  have hout : ‖WithLp.toLp 2 (actualSourceWeights*ᵥinput)‖^2=
      ((3+Real.sqrt 5)/2)*(1+actualGoldenRatio^2) := by
    rw [squared_norm_of_coordinates,actual_source_weights_coordinate_energy]
    have hg := actual_source_spectral_quadratic_gap 1 actualGoldenRatio
    norm_num [input] at hg ⊢
    nlinarith
  have hsquared : ‖WithLp.toLp 2 (actualSourceWeights*ᵥinput)‖^2 ≤
      ‖actualSourceWeights‖^2*‖WithLp.toLp 2 input‖^2 := by
    have hn : 0 ≤ ‖actualSourceWeights‖*‖WithLp.toLp 2 input‖ := by positivity
    nlinarith [norm_nonneg (WithLp.toLp 2 (actualSourceWeights*ᵥinput))]
  rw [hin,hout] at hsquared
  have hlow : (3+Real.sqrt 5)/2 ≤ ‖actualSourceWeights‖^2 := by
    exact (mul_le_mul_iff_left₀ (show 0 < 1+actualGoldenRatio^2 by positivity)).mp (by simpa only [mul_comm] using hsquared)
  have hu : ‖actualSourceWeights‖^2 ≤ (3+Real.sqrt 5)/2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3+Real.sqrt (5:ℝ))/2 by positivity),
      Real.sqrt_nonneg ((3+Real.sqrt (5:ℝ))/2),norm_nonneg actualSourceWeights]
  exact le_antisymm hu hlow

theorem actual_source_spectral_norm_squared_rounds_to_2_618 :
    |‖actualSourceWeights‖^2-(1309/500:ℝ)| < 1/2000 := by
  rw [actual_source_spectral_norm_squared,abs_lt]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

end SafeLearning.CompleteModulesSLLSpectral
