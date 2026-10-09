import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace SafeLearning.CompleteLyapunovInterpolation

theorem genuine_closed_loop_increment_bound {X U : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup U]
    (V : X → ℝ) (f : X × U → X) (policy : X → U)
    (LV LF LP : ℝ) (hVnonneg : 0 ≤ LV) (hfnonneg : 0 ≤ LF)
    (hV : ∀ x y, |V x - V y| ≤ LV * ‖x - y‖)
    (hf : ∀ x y u v, ‖f (x, u) - f (y, v)‖ ≤ LF * (‖x - y‖ + ‖u - v‖))
    (hp : ∀ x y, ‖policy x - policy y‖ ≤ LP * ‖x - y‖) (x y : X) :
    |(V (f (x, policy x)) - V x) - (V (f (y, policy y)) - V y)| ≤
      (LV * LF * (LP + 1) + LV) * ‖x - y‖ := by
  have hj := hf x y (policy x) (policy y)
  have hh := hp x y
  have hvf := hV (f (x, policy x)) (f (y, policy y))
  have hvx := hV x y
  have hnorm : ‖f (x, policy x) - f (y, policy y)‖ ≤
      LF * (LP + 1) * ‖x - y‖ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm hVnonneg
  calc
    _ = |(V (f (x, policy x)) - V (f (y, policy y))) - (V x - V y)| := by
      congr 1
      ring
    _ ≤ |V (f (x, policy x)) - V (f (y, policy y))| + |V x - V y| :=
      abs_sub _ _
    _ ≤ LV * (LF * (LP + 1) * ‖x - y‖) + LV * ‖x - y‖ := by linarith
    _ = _ := by ring

theorem literal_source_composite_margin_and_tests :
    (2 : ℝ) * (11 / 10) * (4 + 1) + 2 = 13 ∧
      (13 : ℝ) * (1 / 100) = 13 / 100 ∧
      (35 / 100 : ℝ) < 1 / 2 - 13 / 100 ∧
      (∀ u : ℝ, 0 ≤ u → ¬u < 1 / 10 - 13 / 100) := by
  norm_num
  intro u hu
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def segment (F : E → E) (dt : ℝ) (x : E) (s : ℝ) : E := x + s • (dt • F x)
def increment (V : E → ℝ) (F : E → E) (dt : ℝ) (x : E) : ℝ :=
  V (x + dt • F x) - V x

theorem genuine_segment_chain_rule (V : E → ℝ) (gradient F : E → E)
    (dt : ℝ) (hV : ∀ z, HasFDerivAt V (innerSL ℝ (gradient z)) z) (x : E) (s : ℝ) :
    HasDerivAt (fun t => V (segment F dt x t))
      (inner ℝ (gradient (segment F dt x s)) (dt • F x)) s := by
  have hp : HasDerivAt (segment F dt x) (dt • F x) s := by
    change HasDerivAt (fun t => x + t • (dt • F x)) (dt • F x) s
    convert
      (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const (dt • F x))
      using 1 <;> (try funext t) <;> simp [Pi.add_apply, id_eq]
  simpa [Function.comp_def, real_inner_smul_right] using
    (hV (segment F dt x s)).comp_hasDerivAt s hp

theorem genuine_increment_integral (V : E → ℝ) (gradient F : E → E)
    (dt : ℝ) (hV : ∀ z, HasFDerivAt V (innerSL ℝ (gradient z)) z)
    (hg : Continuous gradient) (x : E) :
    increment V F dt x =
      ∫ s in (0 : ℝ)..1, inner ℝ (gradient (segment F dt x s)) (dt • F x) := by
  have hp : Continuous (segment F dt x) := by
    unfold segment
    fun_prop
  have hc : Continuous (fun s => inner ℝ (gradient (segment F dt x s)) (dt • F x)) :=
    (hg.comp hp).inner continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun s _ => genuine_segment_chain_rule V gradient F dt hV x s)
    (hc.intervalIntegrable 0 1)
  simpa [increment, segment] using h.symm

theorem literal_source_small_step_constants :
    (1 / 100 : ℝ) * (2 * 1 * (1 + (1 / 100) * 3) + 2 * 3) = 403 / 5000 ∧
      (2 : ℝ) * (1 + (1 / 100) * 3 + 1) = 203 / 50 ∧
      (50 : ℝ) < (203 / 50) / (403 / 5000) ∧
      (203 / 50 : ℝ) / (403 / 5000) < 51 := by
  norm_num

end SafeLearning.CompleteLyapunovInterpolation
