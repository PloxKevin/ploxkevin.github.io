import SafeLearning.CompleteAppliedPendulumSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedPendulumNumerics
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumSampling

theorem actual_pendulum_continuous_root_nearest_three_decimal_enclosures :
    |uprightPlus-3113/1000|<1/2000 ∧
      |uprightMinus-(-3213/1000)|<1/2000 ∧
      |hangingPlus.im-3162/1000|<1/2000 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hp:=Real.sqrt_nonneg (4001:ℝ)
  have ht:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hq:=Real.sqrt_nonneg (3999:ℝ)
  simp only [hangingPlus,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  dsimp [uprightPlus,uprightMinus]
  norm_num
  constructor
  · rw [abs_lt];constructor <;> nlinarith
  constructor <;> rw [abs_lt] <;> constructor <;> nlinarith

theorem actual_pendulum_euler_nearest_three_decimal_enclosures :
    |uprightEulerPlus-1311/1000|<1/2000 ∧
      |uprightEulerMinus-679/1000|<1/2000 ∧
      |hangingEulerPlus.im-316/1000|<1/2000 ∧
      |‖hangingEulerPlus‖-1044/1000|<1/2000 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hp:=Real.sqrt_nonneg (4001:ℝ)
  have ht:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hq:=Real.sqrt_nonneg (3999:ℝ)
  have hn:=Complex.normSq_eq_norm_sq hangingEulerPlus
  rw [actual_hanging_euler_moduli_exceed_one.2.2.1] at hn
  have hn0:=norm_nonneg hangingEulerPlus
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [uprightEulerPlus,uprightPlus];rw [abs_lt];constructor <;> nlinarith
  · dsimp [uprightEulerMinus,uprightMinus];rw [abs_lt];constructor <;> nlinarith
  · norm_num [hangingEulerPlus,hangingPlus]
    rw [abs_lt];constructor <;> nlinarith
  · rw [abs_lt];constructor <;> nlinarith

theorem actual_pendulum_root_and_euler_displays_are_strictly_approximations :
    uprightPlus≠3113/1000 ∧ uprightMinus≠(-3213/1000) ∧
      hangingPlus.im≠3162/1000 ∧ hangingEulerPlus.im≠316/1000 ∧
      ‖hangingEulerPlus‖≠1044/1000 ∧
      uprightEulerPlus≠1311/1000 ∧ uprightEulerMinus≠679/1000 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have ht:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hn:=Complex.normSq_eq_norm_sq hangingEulerPlus
  rw [actual_hanging_euler_moduli_exceed_one.2.2.1] at hn
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro he;dsimp [uprightPlus] at he;nlinarith
  · intro he;dsimp [uprightMinus] at he;nlinarith
  · intro he;norm_num [hangingPlus] at he;nlinarith
  · intro he;norm_num [hangingEulerPlus,hangingPlus] at he;nlinarith
  · intro he;rw [he] at hn;norm_num at hn
  · intro he;dsimp [uprightEulerPlus,uprightPlus] at he;nlinarith
  · intro he;dsimp [uprightEulerMinus,uprightMinus] at he;nlinarith

theorem actual_exact_sample_modulus_rounds_to_point_nine_nine_five_but_is_larger :
    |Real.exp (-(1/200))-995/1000|<1/2000 ∧ 995/1000<Real.exp (-(1/200)) := by
  have hlo : (995/1000:ℝ)<Real.exp (-(1/200)) := by
    have h:=Real.add_one_lt_exp (show (-(1/200):ℝ)≠0 by norm_num)
    linarith
  have hpos:=Real.exp_pos (1/200:ℝ)
  have hle:=Real.add_one_le_exp (1/200:ℝ)
  have hi : Real.exp (-(1/200:ℝ))≤200/201 := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  refine ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,hlo⟩

end SafeLearning.CompleteAppliedPendulumNumerics
