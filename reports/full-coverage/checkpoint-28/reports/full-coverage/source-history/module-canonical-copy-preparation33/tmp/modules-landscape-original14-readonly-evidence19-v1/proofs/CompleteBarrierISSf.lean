import Mathlib
import SafeLearning.CompleteBarrierAbsolutelyContinuous
import SafeLearning.CompleteCoreControl

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SafeLearning.CompleteBarrierISSf

def alpha (r : ℝ) : ℝ := r
def inflation (r : ℝ) : ℝ := r ^ 2 / 4

theorem genuine_global_issf_trajectory_invariance (x d : ℝ → ℝ) (R horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : AbsolutelyContinuousOnInterval x 0 horizon)
    (hd : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon →
      HasDerivAt x (-x s - x s ^ 4 + x s ^ 2 * d s) s)
    (hb : ∀ᵐ s ∂volume, |d s| ≤ R)
    (h0 : x 0 ≤ 2 + inflation R) :
    ∀ t ∈ Icc 0 horizon, x t ≤ 2 + inflation R := by
  let eta : ℝ → ℝ := fun s => 2 + inflation R - x s
  let etaDot : ℝ → ℝ := fun s => x s + x s ^ 4 - x s ^ 2 * d s
  have hc0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => 2 + inflation R) 0 horizon := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hec : AbsolutelyContinuousOnInterval eta 0 horizon := hc0.sub hc
  have hed : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → HasDerivAt eta (etaDot s) s := by
    filter_upwards [hd] with s hd hs
    convert (hasDerivAt_const s (2+inflation R)).sub (hd hs) using 1 <;>
      (try rfl) <;> dsimp [etaDot] <;> ring
  have heb : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → -1 * eta s ≤ etaDot s := by
    filter_upwards [hb] with s hb hs
    have h := SafeLearning.CompleteCoreControl.input_to_state_square (x s) (d s) R hb
    dsimp [eta,etaDot,inflation]
    linarith
  have hi := SafeLearning.CompleteBarrierAbsolutelyContinuous.genuine_ae_forward_invariance
    eta etaDot 1 horizon hT hec hed heb (by dsimp [eta]; linarith)
  intro t ht
  have h := hi t ht
  dsimp [eta] at h
  linarith

theorem genuine_alpha_extended_class_K :
    Continuous alpha ∧ alpha 0 = 0 ∧ StrictMono alpha := by
  exact ⟨continuous_id,rfl,fun _ _ h => h⟩

theorem genuine_inflation_class_K_infinity :
    Continuous inflation ∧ inflation 0 = 0 ∧ StrictMonoOn inflation (Ici 0) ∧
      Tendsto inflation atTop atTop := by
  refine ⟨by unfold inflation; fun_prop,by norm_num [inflation],?_,?_⟩
  · intro x hx y hy hxy
    dsimp [inflation]
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < y+x)]
  · have h := tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)
    change Tendsto (fun r : ℝ => r ^ 2 / 4) atTop atTop
    simpa only [div_eq_mul_inv] using h.atTop_mul_const (by norm_num : (0 : ℝ) < (4:ℝ)⁻¹)

theorem genuine_inflation_shrinks_with_bound : Tendsto inflation (𝓝 (0 : ℝ)) (𝓝 0) := by
  have h : Continuous inflation := by unfold inflation; fun_prop
  simpa [inflation] using h.tendsto 0

theorem actual_beta_inverse_iota_identity (r : ℝ) :
    -alpha (-r) = r ∧ inflation r = r ^ 2 / 4 := by
  simp [alpha,inflation]

theorem genuine_barrier_has_no_finite_lower_bound (B : ℝ) : ∃ x : ℝ, 2-x < B := by
  exact ⟨3-B,by linarith⟩

end SafeLearning.CompleteBarrierISSf
