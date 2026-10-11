import SafeLearning.CompletePolicyQuadraticCalculus
import SafeLearning.CompletePolicyFeasibleTRPO

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyTRPOCalculus
open CompletePolicyQuadraticDual CompletePolicyQuadraticCalculus CompletePolicyFeasibleTRPO
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_trpo_price_satisfies_zero_lambda_derivative
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun t => actualDual H g b c δ (t,0)) 0 (lambdaZero H g δ) := by
  obtain ⟨hp,hs⟩ := actual_lambda_zero_positive_and_square H hH g hg δ hδ
  have hq := actual_q_positive H hH g hg
  have he : -q H g / (2*(lambdaZero H g δ)^2)+δ=0 := by
    rw [hs]
    field_simp [ne_of_gt hδ,ne_of_gt hq]
    <;> ring
  have hd := actual_dual_lambda_partial H hH g b c δ (lambdaZero H g δ) 0 hp
  simp only [zero_smul,sub_zero] at hd
  change HasDerivAt (fun t => actualDual H g b c δ (t,0))
    (-q H g / (2*(lambdaZero H g δ)^2)+δ) (lambdaZero H g δ) at hd
  rwa [he] at hd

theorem actual_trpo_boundary_nu_derivative_and_sign
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ)
    (hf : c+r H g b*Real.sqrt (2*δ/q H g) ≤ 0) :
    HasDerivAt (fun t => actualDual H g b c δ (lambdaZero H g δ,t))
      (-(lambdaZero H g δ*c+r H g b)/lambdaZero H g δ) 0 ∧
    0 ≤ -(lambdaZero H g δ*c+r H g b)/lambdaZero H g δ ∧
    lambdaZero H g δ*c+r H g b ≤ 0 := by
  have hp := (actual_lambda_zero_positive_and_square H hH g hg δ hδ).1
  have hscale := actual_lambda_reciprocal_is_printed_trpo_scale H g δ
  have hmul := mul_nonpos_of_nonneg_of_nonpos hp.le hf
  have he : lambdaZero H g δ*(c+r H g b*Real.sqrt (2*δ/q H g)) =
      lambdaZero H g δ*c+r H g b := by
    rw [←hscale]
    field_simp [ne_of_gt hp]
    <;> ring
  rw [he] at hmul
  refine ⟨?_,div_nonneg (neg_nonneg.mpr hmul) hp.le,hmul⟩
  have hd := actual_dual_nu_partial H hH g b c δ (lambdaZero H g δ) 0 hp
  convert hd using 1
  simp only [zero_mul,zero_sub,r]
  field_simp [ne_of_gt hp]
  <;> ring

theorem actual_trpo_reward_and_dual_are_the_printed_square_root
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (g b : ι → ℝ) (hg : g ≠ 0)
    (c δ : ℝ) (hδ : 0 < δ) :
    g ⬝ᵥ trpo H g b δ=Real.sqrt (2*q H g*δ) ∧
    actualDual H g b c δ (lambdaZero H g δ,0)=Real.sqrt (2*q H g*δ) := by
  have hq := actual_q_positive H hH g hg
  have he : g ⬝ᵥ trpo H g b δ = Real.sqrt (2*δ/q H g)*q H g := by
    rw [actual_trpo_is_literal_inverse_gradient_step,dotProduct_smul]
    rfl
  have hn : 0 ≤ Real.sqrt (2*δ/q H g)*q H g := by positivity
  have hs : (Real.sqrt (2*δ/q H g)*q H g)^2=2*q H g*δ := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hq]
    <;> ring
  have hr : g ⬝ᵥ trpo H g b δ=Real.sqrt (2*q H g*δ) := by
    rw [he,←hs,Real.sqrt_sq hn]
  exact ⟨hr,(actual_trpo_reward_equals_its_true_dual_value H hH g b hg c δ hδ).trans hr⟩

end SafeLearning.CompletePolicyTRPOCalculus
