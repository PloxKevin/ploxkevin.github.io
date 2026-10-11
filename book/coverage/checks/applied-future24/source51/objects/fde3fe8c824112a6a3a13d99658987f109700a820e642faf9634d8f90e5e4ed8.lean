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
  have hz : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply];ring
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
  simpa [realificationHom,realification,Complex.cos_ofReal_re,Complex.sin_ofReal_re] using h.symm

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

theorem actual_source_exponential_is_orthogonal_and_has_norm_one :
    (NormedSpace.exp sourceSkew)ᴴ*NormedSpace.exp sourceSkew=1 ∧
      ‖NormedSpace.exp sourceSkew‖=1 := by
  have he:=actual_skew_matrix_exponential_is_the_true_rotation (1/5)
  change NormedSpace.exp sourceSkew=!![Real.cos (1/5),-Real.sin (1/5);Real.sin (1/5),Real.cos (1/5)] at he
  have hg : (NormedSpace.exp sourceSkew)ᴴ*NormedSpace.exp sourceSkew=1 := by
    rw [he]
    ext i j;fin_cases i <;>fin_cases j <;>
      simp [mul_apply,Fin.sum_univ_two,one_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (1/5:ℝ)]
  have hn:=Matrix.l2_opNorm_conjTranspose_mul_self (NormedSpace.exp sourceSkew)
  rw [hg,norm_one] at hn
  exact ⟨hg,by nlinarith [norm_nonneg (NormedSpace.exp sourceSkew)]⟩

theorem actual_source_matrix_exponential_remainder_is_below_the_literal_rational_bound :
    ‖NormedSpace.exp sourceSkew-sourceTaylor‖≤1/750 := by
  have hc:=actual_real_cosine_uniform_rational_error (1/5) (by norm_num)
  have hs:=actual_real_sine_degree_thirteen_remainder (1/5) (by norm_num)
  norm_num [cosPoly,sinPoly] at hc hs
  have hca : |Real.cos (1/5)-49/50|≤(1/15000:ℝ) := by
    rw [abs_le];constructor <;>linarith [(abs_le.mp hc).1,(abs_le.mp hc).2]
  have hsa : |Real.sin (1/5)-1/5|≤(1/751:ℝ) := by
    rw [abs_le];constructor <;>linarith [(abs_le.mp hs).1,(abs_le.mp hs).2]
  let z : ℂ := ⟨Real.cos (1/5)-49/50,Real.sin (1/5)-1/5⟩
  have he : NormedSpace.exp sourceSkew-sourceTaylor=realification z := by
    rw [show NormedSpace.exp sourceSkew=!![Real.cos (1/5),-Real.sin (1/5);Real.sin (1/5),Real.cos (1/5)] from
      actual_skew_matrix_exponential_is_the_true_rotation (1/5),actual_source_square_taylor_and_gram.2.1]
    ext i j;fin_cases i <;>fin_cases j <;>simp [realification,z] <;>ring
  rw [he,actual_realification_has_the_true_complex_operator_norm]
  have hn : ‖z‖^2=(Real.cos (1/5)-49/50)^2+(Real.sin (1/5)-1/5)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply];simp [z];ring
  have hcs : (Real.cos (1/5)-49/50)^2≤(1/15000:ℝ)^2 := by
    nlinarith [(abs_le.mp hca).1,(abs_le.mp hca).2]
  have hss : (Real.sin (1/5)-1/5)^2≤(1/751:ℝ)^2 := by
    nlinarith [(abs_le.mp hsa).1,(abs_le.mp hsa).2]
  have hsum : (1/15000:ℝ)^2+(1/751:ℝ)^2<(1/750:ℝ)^2 := by norm_num
  nlinarith [norm_nonneg z]

theorem actual_source_remainder_bound_gives_the_looser_layer_bound :
    ‖sourceTaylor‖≤1+(1/5:ℝ)^3/6 ∧
      ‖sourceTaylor‖≤100133333/100000000 ∧ (1/5:ℝ)^3/6≠133333/100000000 := by
  have h:=actual_source_matrix_exponential_remainder_is_below_the_literal_rational_bound
  have hn:=norm_sub_norm_le sourceTaylor (NormedSpace.exp sourceSkew)
  rw [actual_source_exponential_is_orthogonal_and_has_norm_one.2,norm_sub_rev] at hn
  have hsmall:=actual_source_taylor_norm_and_rounding.2.2
  refine ⟨by norm_num;linarith,by rw [abs_lt] at hsmall;linarith [hsmall.2],by norm_num⟩

def sourceStack (activation : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  | 0,x => x
  | n+1,x => activation n (WithLp.toLp 2 (sourceTaylor *ᵥ (sourceStack activation n x)))

theorem actual_arbitrary_nonexpansive_activations_have_the_true_prefix_product_bound
    (activation : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hactivation : ∀ n x y,‖activation n x-activation n y‖≤‖x-y‖)
    (gain : ℝ) (hgain : ‖sourceTaylor‖≤gain) (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖sourceStack activation n x-sourceStack activation n y‖≤gain^n*‖x-y‖ := by
  have hg0 : 0≤gain := (norm_nonneg _).trans hgain
  induction n with
  | zero => simp [sourceStack]
  | succ n ih =>
    have hm:=Matrix.l2_opNorm_mulVec sourceTaylor (sourceStack activation n x-sourceStack activation n y)
    have hs:=hactivation n
      (WithLp.toLp 2 (sourceTaylor *ᵥ sourceStack activation n x))
      (WithLp.toLp 2 (sourceTaylor *ᵥ sourceStack activation n y))
    calc
      _≤‖WithLp.toLp 2 (sourceTaylor *ᵥ (sourceStack activation n x-sourceStack activation n y))‖ := by
        simpa only [sourceStack,←WithLp.toLp_sub,←Matrix.mulVec_sub] using hs
      _≤‖sourceTaylor‖*‖sourceStack activation n x-sourceStack activation n y‖ := by
        simpa only [EuclideanSpace.equiv,PiLp.continuousLinearEquiv_symm_apply,WithLp.ofLp_sub] using hm
      _≤gain*(gain^n*‖x-y‖) := mul_le_mul hgain ih (norm_nonneg _) hg0
      _=gain^(n+1)*‖x-y‖ := by rw [pow_succ];ring

theorem actual_ten_layer_exact_and_remainder_bounds
    (activation : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hactivation : ∀ n x y,‖activation n x-activation n y‖≤‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖sourceStack activation 10 x-sourceStack activation 10 y‖≤
      (Real.sqrt (2501/2500))^10*‖x-y‖ ∧
    ‖sourceStack activation 10 x-sourceStack activation 10 y‖≤
      (1+(1/5:ℝ)^3/6)^10*‖x-y‖ := by
  exact ⟨actual_arbitrary_nonexpansive_activations_have_the_true_prefix_product_bound activation hactivation
    _ actual_source_taylor_norm_and_rounding.1.le 10 x y,
    actual_arbitrary_nonexpansive_activations_have_the_true_prefix_product_bound activation hactivation
    _ actual_source_remainder_bound_gives_the_looser_layer_bound.1 10 x y⟩

theorem actual_ten_layer_product_roundings_and_strict_gain :
    (Real.sqrt (2501/2500))^10=(2501/2500:ℝ)^5 ∧
    |(Real.sqrt (2501/2500))^10-100200160/100000000|<1/200000000 ∧
    |(1+(1/5:ℝ)^3/6)^10-101341362/100000000|<1/200000000 ∧
    1<(Real.sqrt (2501/2500))^10 := by
  have he : (Real.sqrt (2501/2500))^10=(2501/2500:ℝ)^5 := by
    rw [show (10:ℕ)=2*5 by norm_num,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ)≤2501/2500)]
  rw [he]
  norm_num

theorem actual_identity_activation_stack_is_the_true_taylor_power
    (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    sourceStack (fun _ x=>x) n x=WithLp.toLp 2 (sourceTaylor^n *ᵥ x) := by
  induction n with
  | zero => simp [sourceStack]
  | succ n ih => simp only [sourceStack,ih,WithLp.ofLp_toLp,pow_succ',Matrix.mulVec_mulVec]

theorem actual_identity_activation_ten_matrix_gain_is_strictly_greater_than_one :
    ‖sourceTaylor^10‖=(Real.sqrt (2501/2500))^10 ∧ 1<‖sourceTaylor^10‖ := by
  let z : ℂ := ⟨49/50,1/5⟩
  have hs : sourceTaylor=realificationHom z := by
    rw [actual_source_square_taylor_and_gram.2.1]
    rfl
  have hp : sourceTaylor^10=realification (z^10) := by
    rw [hs,←map_pow];rfl
  have hnorm : ‖sourceTaylor^10‖=‖sourceTaylor‖^10 := by
    rw [hp,actual_realification_has_the_true_complex_operator_norm,norm_pow,hs]
    change ‖z‖^10=‖realification z‖^10
    rw [actual_realification_has_the_true_complex_operator_norm]
  rw [actual_source_taylor_norm_and_rounding.1] at hnorm
  exact ⟨hnorm,by rw [hnorm];exact actual_ten_layer_product_roundings_and_strict_gain.2.2.2⟩

end SafeLearning.CompleteModulesDesignTruncation
