import Mathlib
import SafeLearning.CompleteLyapunovInterpolation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology NNReal

namespace SafeLearning.CompleteLyapunovSmallStep
open SafeLearning.CompleteLyapunovInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem genuine_segment_distance_bound (F : E → E) (LF : ℝ≥0)
    (hF : LipschitzWith LF F) (dt : ℝ) (hdt : 0 ≤ dt)
    (x y : E) (s : ℝ) (hs : s ∈ Icc 0 1) :
    ‖SafeLearning.CompleteLyapunovInterpolation.segment F dt x s - SafeLearning.CompleteLyapunovInterpolation.segment F dt y s‖ ≤
      (1 + dt * (LF : ℝ)) * ‖x - y‖ := by
  have hf : ‖F x - F y‖ ≤ (LF : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hF.dist_le_mul x y
  calc
    _ = ‖(x - y) + (s * dt) • (F x - F y)‖ := by
      congr 1
      simp only [SafeLearning.CompleteLyapunovInterpolation.segment, smul_sub, smul_smul]
      abel
    _ ≤ ‖x - y‖ + ‖(s * dt) • (F x - F y)‖ := norm_add_le _ _
    _ = ‖x - y‖ + s * dt * ‖F x - F y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs.1 hdt)]
    _ ≤ ‖x - y‖ + s * dt * ((LF : ℝ) * ‖x - y‖) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hf (mul_nonneg hs.1 hdt)) _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hs.2
        (show 0 ≤ dt * ((LF : ℝ) * ‖x - y‖) by positivity)
      nlinarith

theorem genuine_Euler_map_lipschitz_bound (F : E → E) (LF : ℝ≥0)
    (hF : LipschitzWith LF F) (dt : ℝ) (hdt : 0 ≤ dt) (x y : E) :
    ‖(x + dt • F x) - (y + dt • F y)‖ ≤
      (1 + dt * (LF : ℝ)) * ‖x - y‖ := by
  simpa [SafeLearning.CompleteLyapunovInterpolation.segment] using genuine_segment_distance_bound F LF hF dt hdt x y 1
    (by norm_num)

theorem genuine_integrand_difference_bound (gradient F : E → E)
    (M LF LV Fmax : ℝ≥0) (hg : LipschitzWith M gradient) (hF : LipschitzWith LF F)
    (hbG : ∀ z, ‖gradient z‖ ≤ (LV : ℝ)) (hbF : ∀ z, ‖F z‖ ≤ (Fmax : ℝ))
    (dt : ℝ) (hdt : 0 ≤ dt) (x y : E) (s : ℝ) (hs : s ∈ Icc 0 1) :
    |inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s)) (dt • F x) -
      inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • F y)| ≤
      dt * ((M : ℝ) * Fmax * (1 + dt * LF) + (LV : ℝ) * LF) * ‖x - y‖ := by
  have hpath := genuine_segment_distance_bound F LF hF dt hdt x y s hs
  have hgdiff : ‖gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s) - gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)‖ ≤
      (M : ℝ) * (1 + dt * LF) * ‖x - y‖ := by
    have h := hg.dist_le_mul (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s) (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)
    simp only [dist_eq_norm] at h
    have hh := mul_le_mul_of_nonneg_left hpath M.coe_nonneg
    nlinarith
  have hFdiff : ‖F x - F y‖ ≤ (LF : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hF.dist_le_mul x y
  have hscale : ‖dt • F x‖ ≤ dt * (Fmax : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdt]
    exact mul_le_mul_of_nonneg_left (hbF x) hdt
  have hscalediff : ‖dt • (F x - F y)‖ ≤ dt * ((LF : ℝ) * ‖x - y‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdt]
    exact mul_le_mul_of_nonneg_left hFdiff hdt
  calc
    _ = |inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s) - gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • F x) +
      inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • (F x - F y))| := by
        congr 1
        simp only [inner_sub_left, inner_sub_right, smul_sub]
        ring
    _ ≤ |inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s) - gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • F x)| +
      |inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • (F x - F y))| := abs_add_le _ _
    _ ≤ ‖gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s) - gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)‖ * ‖dt • F x‖ +
      ‖gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)‖ * ‖dt • (F x - F y)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ((M : ℝ) * (1 + dt * LF) * ‖x - y‖) * (dt * Fmax) +
      (LV : ℝ) * (dt * ((LF : ℝ) * ‖x - y‖)) := by
        apply add_le_add
        · exact mul_le_mul hgdiff hscale (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hbG _) hscalediff (norm_nonneg _) LV.coe_nonneg
    _ = _ := by ring

theorem genuine_small_step_increment_bound (V : E → ℝ) (gradient F : E → E)
    (M LF LV Fmax : ℝ≥0) (hg : LipschitzWith M gradient) (hF : LipschitzWith LF F)
    (hbG : ∀ z, ‖gradient z‖ ≤ (LV : ℝ)) (hbF : ∀ z, ‖F z‖ ≤ (Fmax : ℝ))
    (hV : ∀ z, HasFDerivAt V (innerSL ℝ (gradient z)) z)
    (dt : ℝ) (hdt : 0 ≤ dt) (x y : E) :
    |increment V F dt x - increment V F dt y| ≤
      dt * ((M : ℝ) * Fmax * (1 + dt * LF) + (LV : ℝ) * LF) * ‖x - y‖ := by
  have hc : ∀ z : E, Continuous
      (fun s : ℝ => inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt z s)) (dt • F z)) := by
    intro z
    have hp : Continuous (SafeLearning.CompleteLyapunovInterpolation.segment F dt z) := by unfold SafeLearning.CompleteLyapunovInterpolation.segment; fun_prop
    exact (hg.continuous.comp hp).inner continuous_const
  rw [genuine_increment_integral V gradient F dt hV hg.continuous x,
    genuine_increment_integral V gradient F dt hV hg.continuous y,
    ← intervalIntegral.integral_sub ((hc x).intervalIntegrable 0 1)
      ((hc y).intervalIntegrable 0 1)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ => inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt x s)) (dt • F x) -
      inner ℝ (gradient (SafeLearning.CompleteLyapunovInterpolation.segment F dt y s)) (dt • F y))
    (C := dt * ((M : ℝ) * Fmax * (1 + dt * LF) + (LV : ℝ) * LF) * ‖x - y‖)
    (a := (0 : ℝ)) (b := 1) (fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioc] at hs
        exact ⟨hs.1.le, hs.2⟩
      simpa only [Real.norm_eq_abs] using
        genuine_integrand_difference_bound gradient F M LF LV Fmax hg hF hbG hbF
          dt hdt x y s hs')
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

end SafeLearning.CompleteLyapunovSmallStep
