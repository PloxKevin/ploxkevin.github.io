import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierAEComparison

/-- A one-sided linear derivative bound is needed only outside the safe set.
Absolute continuity and the actual a.e. derivative supply the comparison argument. -/
theorem genuine_ae_one_sided_invariance (z v : ℝ → ℝ) (a b L : ℝ)
    (hab : a≤b) (hc : AbsolutelyContinuousOnInterval z a b)
    (hd : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt z (v s) s)
    (hb : ∀ᵐ s ∂volume, s ∈ Icc a b → 0<z s → v s≤L*z s)
    (h0 : z a≤0) : ∀ t ∈ Icc a b, z t≤0 := by
  intro t ht
  by_contra hbad
  have hzt : 0<z t := lt_of_not_ge hbad
  let K : Set ℝ := Icc a t ∩ z ⁻¹' Iic 0
  have hct : ContinuousOn z (Icc a t) := by
    apply hc.continuousOn.mono
    rw [uIcc_of_le hab]
    intro s hs
    exact ⟨hs.1,hs.2.trans ht.2⟩
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hct.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) inter_subset_left
  have haK : a ∈ K := ⟨⟨le_rfl,ht.1⟩,h0⟩
  obtain ⟨c,hcK,hmax⟩ := hK.exists_isMaxOn ⟨a,haK⟩ continuous_id.continuousOn
  have hca : a≤c := hcK.1.1
  have hct' : c≤t := hcK.1.2
  have hzc : z c≤0 := hcK.2
  have hpositive : ∀ s ∈ Icc c t, s≠c → 0<z s := by
    intro s hs hne
    by_contra h
    have hsK : s ∈ K := ⟨⟨hca.trans hs.1,hs.2⟩,le_of_not_gt h⟩
    have hsle : s≤c := hmax hsK
    exact hne (le_antisymm hsle hs.1)
  have hcz : AbsolutelyContinuousOnInterval z c t := hc.mono (by
    rw [uIcc_of_le hct',uIcc_of_le hab]
    intro s hs
    exact ⟨hca.trans hs.1,hs.2.trans ht.2⟩)
  have he : AbsolutelyContinuousOnInterval (fun s : ℝ => Real.exp (-L*s)) c t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  let g : ℝ → ℝ := fun s => -(Real.exp (-L*s)*z s)
  have hg : AbsolutelyContinuousOnInterval g c t := (he.mul hcz).neg
  have hne : ∀ᵐ s : ℝ ∂volume, s≠c := by rw [ae_iff]; simp
  have hder : ∀ᵐ s ∂volume, s ∈ Icc c t → 0≤deriv g s := by
    filter_upwards [hd,hb,hne] with s hd hb hne hs
    have hsab : s ∈ Icc a b := ⟨hca.trans hs.1,hs.2.trans ht.2⟩
    have hds : HasDerivAt g (Real.exp (-L*s)*(L*z s-v s)) s := by
      convert ((((hasDerivAt_id s).const_mul (-L)).exp).mul (hd hsab)).neg using 1 <;>
        (try rfl) <;> dsimp [g] <;> ring
    rw [hds.deriv]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hb hsab (hpositive s hs hne)])
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict hct'
    ((ae_restrict_iff' measurableSet_Icc).mpr hder)
  rw [hg.integral_deriv_eq_sub] at hi
  have hgc : 0≤g c := by dsimp [g]; exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hzc)
  have hgt : 0≤g t := by linarith
  have hnegative : g t<0 := by dsimp [g]; exact neg_neg_of_pos (mul_pos (Real.exp_pos _) hzt)
  linarith

end SafeLearning.CompleteBarrierAEComparison
