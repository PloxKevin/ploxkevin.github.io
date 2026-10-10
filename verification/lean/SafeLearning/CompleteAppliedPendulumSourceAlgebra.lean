import SafeLearning.CompleteAppliedPendulumNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedPendulumSourceAlgebra
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumSampling

theorem actual_printed_upright_quadratic_formula_is_the_true_unrounded_root_pair :
    (-1/10+Real.sqrt ((1/100:ℝ)+40))/2=uprightPlus ∧
      (-1/10-Real.sqrt ((1/100:ℝ)+40))/2=uprightMinus := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have ht:=Real.sq_sqrt (by norm_num : (0:ℝ)≤(1/100:ℝ)+40)
  have hp:=Real.sqrt_nonneg (4001:ℝ)
  have hq:=Real.sqrt_nonneg ((1/100:ℝ)+40)
  have he : Real.sqrt ((1/100:ℝ)+40)=Real.sqrt 4001/10 := by nlinarith
  rw [he]
  dsimp [uprightPlus,uprightMinus]
  constructor <;> ring

theorem actual_exact_hanging_and_euler_root_displays :
    hangingPlus=(-1+(Real.sqrt 3999:ℝ)*Complex.I)/20 ∧
      hangingMinus=(-1-(Real.sqrt 3999:ℝ)*Complex.I)/20 ∧
      hangingEulerPlus=(199+(Real.sqrt 3999:ℝ)*Complex.I)/200 ∧
      hangingEulerMinus=(199-(Real.sqrt 3999:ℝ)*Complex.I)/200 := by
  dsimp [hangingEulerPlus,hangingEulerMinus,hangingPlus,hangingMinus]
  refine ⟨?_,?_,?_,?_⟩ <;> push_cast <;> ring

theorem actual_euler_modulus_squared_is_the_literal_expanded_source_identity :
    Complex.normSq hangingEulerPlus=
      1+2*(1/10)*hangingPlus.re+(1/100)*Complex.normSq hangingPlus ∧
      1+2*(1/10)*hangingPlus.re+(1/100)*Complex.normSq hangingPlus=(109/100:ℝ) := by
  have hn:=actual_hanging_roots_have_negative_real_parts_and_nonzero_imaginary_parts
  rw [hn.1,hn.2.2.2.2.1,actual_hanging_euler_moduli_exceed_one.2.2.1]
  constructor <;> norm_num

end SafeLearning.CompleteAppliedPendulumSourceAlgebra
