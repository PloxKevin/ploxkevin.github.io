import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignApproximateOrthogonality
variable {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]

def sourceStack (weights : ℕ → Matrix N N ℝ)
    (activation : ℕ → EuclideanSpace ℝ N → EuclideanSpace ℝ N) :
    ℕ → EuclideanSpace ℝ N → EuclideanSpace ℝ N
  | 0,x => x
  | n+1,x => activation n (WithLp.toLp 2 (weights n *ᵥ (sourceStack weights activation n x)))

theorem actual_exact_orthogonality_has_unit_operator_norm
    (Q : Matrix N N ℝ) (hQ : Qᵀ*Q=1) : ‖Q‖=1 := by
  have h:=Matrix.l2_opNorm_conjTranspose_mul_self Q
  have hc : Qᴴ=Qᵀ := by ext i j;simp
  rw [hc,hQ,norm_one] at h
  nlinarith [norm_nonneg Q]

theorem actual_implemented_operator_norm_bound
    (Q implemented : Matrix N N ℝ) (hQ : Qᵀ*Q=1)
    (herror : ‖implemented-Q‖≤1/500) : ‖implemented‖≤501/500 := by
  calc
    ‖implemented‖=‖(implemented-Q)+Q‖ := by congr 1;abel
    _ ≤ ‖implemented-Q‖+‖Q‖ := norm_add_le _ _
    _ ≤ (1/500:ℝ)+1 := add_le_add herror (actual_exact_orthogonality_has_unit_operator_norm Q hQ).le
    _ = _ := by norm_num

theorem actual_every_prefix_stack_gain_with_the_operator_error_allowance
    (Q implemented : ℕ → Matrix N N ℝ)
    (activation : ℕ → EuclideanSpace ℝ N → EuclideanSpace ℝ N)
    (hQ : ∀ n<6,(Q n)ᵀ*Q n=1)
    (herror : ∀ n<6,‖implemented n-Q n‖≤1/500)
    (hactivation : ∀ n<6,∀ x y,‖activation n x-activation n y‖≤‖x-y‖)
    (n : ℕ) (hn : n≤6) (x y : EuclideanSpace ℝ N) :
    ‖sourceStack implemented activation n x-sourceStack implemented activation n y‖≤
      (501/500:ℝ)^n*‖x-y‖ := by
  induction n with
  | zero => simp [sourceStack]
  | succ n ih =>
    have hlt : n<6 := by omega
    have hi:=ih (by omega)
    have hg:=actual_implemented_operator_norm_bound (Q n) (implemented n) (hQ n hlt) (herror n hlt)
    have hm:=Matrix.l2_opNorm_mulVec (implemented n)
      (sourceStack implemented activation n x-sourceStack implemented activation n y)
    have hstep:=hactivation n hlt
      (WithLp.toLp 2 (implemented n *ᵥ sourceStack implemented activation n x))
      (WithLp.toLp 2 (implemented n *ᵥ sourceStack implemented activation n y))
    calc
      _ ≤ ‖WithLp.toLp 2 (implemented n *ᵥ (sourceStack implemented activation n x-
        sourceStack implemented activation n y))‖ := by
        simpa only [sourceStack,←WithLp.toLp_sub,←Matrix.mulVec_sub] using hstep
      _ ≤ ‖implemented n‖*‖sourceStack implemented activation n x-sourceStack implemented activation n y‖ := by
        simpa only [EuclideanSpace.equiv,PiLp.continuousLinearEquiv_symm_apply,
          WithLp.ofLp_sub] using hm
      _ ≤ (501/500:ℝ)*((501/500:ℝ)^n*‖x-y‖) :=
        mul_le_mul hg hi (norm_nonneg _) (by norm_num)
      _ = _ := by rw [pow_succ];ring

theorem actual_external_scale_restores_the_source_budget
    (Q implemented : ℕ → Matrix N N ℝ)
    (activation : ℕ → EuclideanSpace ℝ N → EuclideanSpace ℝ N)
    (hQ : ∀ n<6,(Q n)ᵀ*Q n=1)
    (herror : ∀ n<6,‖implemented n-Q n‖≤1/500)
    (hactivation : ∀ n<6,∀ x y,‖activation n x-activation n y‖≤‖x-y‖)
    (c : ℝ) (hc : 0≤c) (hscale : c≤(3/10)/(501/500:ℝ)^6)
    (x y : EuclideanSpace ℝ N) :
    ‖c • sourceStack implemented activation 6 x-c • sourceStack implemented activation 6 y‖≤
      (3/10)*‖x-y‖ := by
  have hprod : c*(501/500:ℝ)^6≤3/10 :=
    (le_div_iff₀ (by positivity : (0:ℝ)<(501/500)^6)).mp hscale
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  calc
    _ ≤ c*((501/500:ℝ)^6*‖x-y‖) := mul_le_mul_of_nonneg_left
      (actual_every_prefix_stack_gain_with_the_operator_error_allowance Q implemented activation
        hQ herror hactivation 6 le_rfl x y) hc
    _ = (c*(501/500:ℝ)^6)*‖x-y‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

theorem actual_six_stage_product_and_source_roundings
    (Q implemented : Fin 6 → Matrix N N ℝ)
    (hQ : ∀ i,(Q i)ᵀ*Q i=1) (herror : ∀ i,‖implemented i-Q i‖≤1/500) :
    (∏ i,‖implemented i‖)≤(501/500:ℝ)^6 ∧
      |(501/500:ℝ)^6-(1012060/1000000)|<1/2000000 ∧
      |(3/10)/(501/500:ℝ)^6-(296425/1000000)|<1/2000000 := by
  refine ⟨?_,by norm_num,by norm_num⟩
  calc
    _ ≤ ∏ _i : Fin 6,(501/500:ℝ) := Finset.prod_le_prod₀
      (by intro i hi;exact norm_nonneg _) (by intro i hi;exact actual_implemented_operator_norm_bound _ _ (hQ i) (herror i))
    _ = _ := by norm_num

end SafeLearning.CompleteModulesDesignApproximateOrthogonality
