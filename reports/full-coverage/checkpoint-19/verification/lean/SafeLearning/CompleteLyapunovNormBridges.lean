import Mathlib
import SafeLearning.CompleteLyapunovInterpolation
import SafeLearning.CompleteLyapunovSmallStep

set_option autoImplicit false
noncomputable section
open scoped NNReal RealInnerProductSpace

namespace SafeLearning.CompleteLyapunovNormBridges

theorem genuine_concatenated_l1_difference {X U : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup U] (x y : X) (u v : U) :
    ‖WithLp.toLp 1 (x, u) - WithLp.toLp 1 (y, v)‖ = ‖x - y‖ + ‖u - v‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  rfl

theorem genuine_joint_l1_closed_loop_bound {X U : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup U]
    (V : X → ℝ) (f : X × U → X) (policy : X → U)
    (LV LF LP : ℝ≥0)
    (hV : LipschitzWith LV V)
    (hf : LipschitzWith LF (fun z : WithLp 1 (X × U) => f (WithLp.ofLp z)))
    (hp : LipschitzWith LP policy) (x y : X) :
    |(V (f (x, policy x)) - V x) - (V (f (y, policy y)) - V y)| ≤
      ((LV : ℝ) * LF * ((LP : ℝ) + 1) + LV) * ‖x - y‖ := by
  apply SafeLearning.CompleteLyapunovInterpolation.genuine_closed_loop_increment_bound
    V f policy LV LF LP LV.coe_nonneg LF.coe_nonneg
  · intro a b
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hV.dist_le_mul a b
  · intro a b u v
    have h := hf.dist_le_mul (WithLp.toLp 1 (a, u)) (WithLp.toLp 1 (b, v))
    simpa only [dist_eq_norm, WithLp.ofLp_toLp, genuine_concatenated_l1_difference] using h
  · intro a b
    simpa only [dist_eq_norm] using hp.dist_le_mul a b

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem genuine_gradient_bound_implies_lipschitz (V : E → ℝ) (gradient : E → E)
    (LV : ℝ≥0) (hV : ∀ z, HasFDerivAt V (innerSL ℝ (gradient z)) z)
    (hbG : ∀ z, ‖gradient z‖ ≤ (LV : ℝ)) : LipschitzWith LV V := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hV z).differentiableAt)
  intro z
  apply NNReal.coe_le_coe.mp
  simpa only [(hV z).fderiv, coe_nnnorm, innerSL_apply_norm] using hbG z

theorem genuine_small_step_composite_from_gradient_bound (V : E → ℝ)
    (gradient F : E → E) (LV LF : ℝ≥0)
    (hV : ∀ z, HasFDerivAt V (innerSL ℝ (gradient z)) z)
    (hbG : ∀ z, ‖gradient z‖ ≤ (LV : ℝ)) (hF : LipschitzWith LF F)
    (dt : ℝ) (hdt : 0 ≤ dt) (x y : E) :
    |SafeLearning.CompleteLyapunovInterpolation.increment V F dt x -
      SafeLearning.CompleteLyapunovInterpolation.increment V F dt y| ≤
      (LV : ℝ) * (1 + dt * LF + 1) * ‖x - y‖ := by
  have hv := genuine_gradient_bound_implies_lipschitz V gradient LV hV hbG
  have hvx : |V x - V y| ≤ (LV : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hv.dist_le_mul x y
  have hvf : |V (x + dt • F x) - V (y + dt • F y)| ≤
      (LV : ℝ) * ((1 + dt * LF) * ‖x - y‖) := by
    have ha := hv.dist_le_mul (x + dt • F x) (y + dt • F y)
    simp only [dist_eq_norm, Real.norm_eq_abs] at ha
    exact ha.trans (mul_le_mul_of_nonneg_left
      (SafeLearning.CompleteLyapunovSmallStep.genuine_Euler_map_lipschitz_bound
        F LF hF dt hdt x y) LV.coe_nonneg)
  unfold SafeLearning.CompleteLyapunovInterpolation.increment
  calc
    _ = |(V (x + dt • F x) - V (y + dt • F y)) - (V x - V y)| := by congr 1; ring
    _ ≤ |V (x + dt • F x) - V (y + dt • F y)| + |V x - V y| := abs_sub _ _
    _ ≤ _ := by linarith

end SafeLearning.CompleteLyapunovNormBridges
