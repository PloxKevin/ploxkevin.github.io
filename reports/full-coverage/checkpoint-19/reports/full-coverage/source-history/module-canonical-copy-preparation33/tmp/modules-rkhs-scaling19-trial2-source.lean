import Mathlib.Analysis.InnerProductSpace.Reproducing
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open ContinuousLinearMap
namespace SafeLearning.CompleteModulesRKHSScaling
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def scaledRKHS (r : RKHS ℝ H X ℝ) (c : ℝ) (hc : 0 < c) : RKHS ℝ H X ℝ where
  coeCLM := Real.sqrt c • r.coeCLM
  coeCLM_injective := by
    intro f g h
    apply r.coeCLM_injective
    funext x
    have hx := congrFun h x
    change Real.sqrt c * r.coeCLM f x = Real.sqrt c * r.coeCLM g x at hx
    exact mul_left_cancel₀ (Real.sqrt_pos.mpr hc).ne' hx

theorem actual_scaled_rkhs_evaluation_is_the_original_evaluation_times_sqrt_scale
    (r : RKHS ℝ H X ℝ) (c : ℝ) (hc : 0 < c) (f : H) (x : X) :
    (scaledRKHS r c hc).coeCLM f x = Real.sqrt c * r.coeCLM f x := rfl

theorem actual_scaled_rkhs_represents_the_identical_function_with_scaled_coefficients
    (r : RKHS ℝ H X ℝ) (c : ℝ) (hc : 0 < c) (f : H) :
    (scaledRKHS r c hc).coeCLM ((Real.sqrt c)⁻¹ • f) = r.coeCLM f := by
  ext x
  simp only [actual_scaled_rkhs_evaluation_is_the_original_evaluation_times_sqrt_scale,
    map_smul,Pi.smul_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne',one_mul]

theorem actual_same_function_has_its_true_hilbert_norm_divided_by_sqrt_scale
    (c : ℝ) (hc : 0 < c) (f : H) :
    ‖(Real.sqrt c)⁻¹ • f‖ = ‖f‖ / Real.sqrt c := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hc))]
  ring

theorem actual_scaled_rkhs_kernel_sections_are_the_true_sqrt_scaled_sections
    (r : RKHS ℝ H X ℝ) (c : ℝ) (hc : 0 < c) (x : X) :
    letI : RKHS ℝ H X ℝ := scaledRKHS r c hc
    RKHS.kerFun H x = Real.sqrt c • @RKHS.kerFun ℝ _ X ℝ _ _ H _ _ r _ _ x := by
  simp only [RKHS.kerFun,scaledRKHS,ContinuousLinearMap.comp_smul,map_smulₛₗ,
    starRingEnd_apply,star_trivial]

theorem actual_scaled_rkhs_has_the_entire_kernel_scaled_by_c
    (r : RKHS ℝ H X ℝ) (c : ℝ) (hc : 0 < c) :
    letI : RKHS ℝ H X ℝ := scaledRKHS r c hc
    RKHS.kernel H = c • @RKHS.kernel ℝ _ X ℝ _ _ H _ _ r _ _ := by
  letI : RKHS ℝ H X ℝ := scaledRKHS r c hc
  ext x y v
  simp only [RKHS.kernel_apply,
    actual_scaled_rkhs_kernel_sections_are_the_true_sqrt_scaled_sections r c hc,
    map_smulₛₗ,starRingEnd_apply,star_trivial,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul,smul_smul,Real.mul_self_sqrt hc.le,
    Matrix.smul_apply,ContinuousLinearMap.smul_apply]

end SafeLearning.CompleteModulesRKHSScaling
