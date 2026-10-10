import SafeLearning.CompleteModulesDesignEasyMatrices
import SafeLearning.CompleteFoundationsCosineNumerics

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignTruncation
open CompleteModulesDesignEasyMatrices CompleteFoundationsCosineNumerics

def realification (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![z.re,-z.im;z.im,z.re]

def realificationHom : ℂ →+* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := realification
  map_one' := by ext i j;fin_cases i <;> fin_cases j <;> simp [realification,one_apply]
  map_mul' z w := by
    ext i j;fin_cases i <;> fin_cases j <;>
      simp [realification,mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im] <;>ring
  map_zero' := by ext i j;fin_cases i <;> fin_cases j <;> simp [realification]
  map_add' z w := by ext i j;fin_cases i <;> fin_cases j <;> simp [realification] <;>ring

theorem actual_realification_is_continuous : Continuous realificationHom := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [realificationHom,realification] <;> fun_prop

theorem actual_realification_has_the_true_complex_operator_norm (z : ℂ) :
    ‖realification z‖=‖z‖ := by
  have hg : (realification z)ᴴ*realification z=diagonal ![z.re^2+z.im^2,z.re^2+z.im^2] := by
    ext i j;fin_cases i <;> fin_cases j <;>
      simp [realification,mul_apply,Fin.sum_univ_two,conjTranspose_apply,diagonal_apply] <;>ring
  have hn:=Matrix.l2_opNorm_conjTranspose_mul_self (realification z)
  rw [hg,actual_positive_diagonal_operator_norm_is_the_largest_entry
    _ _ (by positivity) (by positivity)] at hn
  simp only [max_self] at hn
  have hz : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm];rfl
  nlinarith [norm_nonneg (realification z),norm_nonneg z]

theorem actual_skew_matrix_exponential_is_the_true_rotation (t : ℝ) :
    NormedSpace.exp (!![0,-t;t,0] : Matrix (Fin 2) (Fin 2) ℝ)=
      !![Real.cos t,-Real.sin t;Real.sin t,Real.cos t] := by
  have h:=NormedSpace.map_exp realificationHom actual_realification_is_continuous
    ((t:ℂ)*Complex.I)
  rw [←Complex.exp_eq_exp_ℂ,Complex.exp_ofReal_mul_I] at h
  have hk : realificationHom ((t:ℂ)*Complex.I)=(!![0,-t;t,0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [realificationHom,realification]
  rw [hk] at h
  exact h.symm

def sourceSkew : Matrix (Fin 2) (Fin 2) ℝ := !![0,-(1/5);1/5,0]
def sourceTaylor : Matrix (Fin 2) (Fin 2) ℝ := 1+sourceSkew+(1/2:ℝ) • sourceSkew^2

theorem actual_source_square_taylor_and_gram :
    sourceSkew^2=-(1/25:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ) ∧
    sourceTaylor=!![49/50,-(1/5);1/5,49/50] ∧
    sourceTaylorᴴ*sourceTaylor=diagonal ![(2501/2500:ℝ),2501/2500] := by
  refine ⟨?_,?_,?_⟩ <;>
    ext i j <;>fin_cases i <;>fin_cases j <;>
      norm_num [sourceTaylor,sourceSkew,pow_two,mul_apply,Fin.sum_univ_two,one_apply,
        conjTranspose_apply,diagonal_apply,Pi.smul_apply,Matrix.smul_apply]

theorem actual_source_taylor_norm_and_rounding :
    ‖sourceTaylor‖=Real.sqrt (2501/2500) ∧ 1<‖sourceTaylor‖ ∧
      |‖sourceTaylor‖-100019998/100000000|<1/200000000 := by
  have hn:=Matrix.l2_opNorm_conjTranspose_mul_self sourceTaylor
  rw [actual_source_square_taylor_and_gram.2.2,
    actual_positive_diagonal_operator_norm_is_the_largest_entry _ _ (by norm_num) (by norm_num)] at hn
  norm_num at hn
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2501/2500)
  have he : ‖sourceTaylor‖=Real.sqrt (2501/2500) := by
    nlinarith [norm_nonneg sourceTaylor,Real.sqrt_nonneg (2501/2500)]
  refine ⟨he,by nlinarith [norm_nonneg sourceTaylor],?_⟩
  rw [abs_lt]
  constructor <;>nlinarith [norm_nonneg sourceTaylor]

end SafeLearning.CompleteModulesDesignTruncation
