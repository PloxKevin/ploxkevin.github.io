import Mathlib

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace SafeLearning.CompleteBarrierAbsolutelyContinuous

theorem genuine_ae_integrating_factor (eta etaDot : ℝ → ℝ) (beta horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : AbsolutelyContinuousOnInterval eta 0 horizon)
    (hd : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → HasDerivAt eta (etaDot s) s)
    (hb : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → -beta * eta s ≤ etaDot s)
    (t : ℝ) (ht : t ∈ Icc 0 horizon) :
    eta 0 * Real.exp (-beta * t) ≤ eta t := by
  have hac : AbsolutelyContinuousOnInterval eta 0 t := hc.mono (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    intro s hs
    exact ⟨hs.1,hs.2.trans ht.2⟩)
  have he : AbsolutelyContinuousOnInterval (fun s : ℝ => Real.exp (beta*s)) 0 t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  let g : ℝ → ℝ := fun s => Real.exp (beta*s) * eta s
  have hg : AbsolutelyContinuousOnInterval g 0 t := he.mul hac
  have hpos : ∀ᵐ s ∂volume, s ∈ Icc 0 t → 0 ≤ deriv g s := by
    filter_upwards [hd,hb] with s hd hb hs
    have hsT : s ∈ Icc 0 horizon := ⟨hs.1,hs.2.trans ht.2⟩
    have hdg : HasDerivAt g (Real.exp (beta*s) * (etaDot s + beta*eta s)) s := by
      convert (((hasDerivAt_id s).const_mul beta).exp).mul (hd hsT) using 1 <;>
        (try rfl) <;> dsimp [g] <;> ring
    rw [hdg.deriv]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hb hsT])
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    ((ae_restrict_iff' measurableSet_Icc).mpr hpos)
  rw [hg.integral_deriv_eq_sub] at hi
  have hfac : eta 0 ≤ Real.exp (beta*t) * eta t := by simpa [g] using hi
  have hmul := mul_le_mul_of_nonneg_left hfac (Real.exp_pos (-beta*t)).le
  have heq : Real.exp (-beta*t) * Real.exp (beta*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [← mul_assoc,heq,one_mul] at hmul
  simpa only [mul_comm] using hmul

theorem genuine_ae_forward_invariance (eta etaDot : ℝ → ℝ) (beta horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : AbsolutelyContinuousOnInterval eta 0 horizon)
    (hd : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → HasDerivAt eta (etaDot s) s)
    (hb : ∀ᵐ s ∂volume, s ∈ Icc 0 horizon → -beta * eta s ≤ etaDot s)
    (h0 : 0 ≤ eta 0) : ∀ t ∈ Icc 0 horizon, 0 ≤ eta t := by
  intro t ht
  exact (mul_nonneg h0 (Real.exp_pos _).le).trans
    (genuine_ae_integrating_factor eta etaDot beta horizon hT hc hd hb t ht)

end SafeLearning.CompleteBarrierAbsolutelyContinuous
