import SafeLearning.CompleteBarrierAEComparison

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierNonlinearComparison

/-- Monotonicity of the nonlinear comparison function gives the needed one-sided
bound, even when its ordinary Lipschitz constant does not exist. -/
theorem genuine_nonlinear_comparison (eta etaDot y alpha : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : Monotone alpha)
    (he : AbsolutelyContinuousOnInterval eta a b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hde : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt eta (etaDot t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt y (-alpha (y t)) t)
    (hineq : ∀ᵐ t ∂volume, t ∈ Icc a b → -alpha (eta t) ≤ etaDot t)
    (h0 : y a ≤ eta a) : ∀ t ∈ Icc a b, y t ≤ eta t := by
  have hd : ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (fun s => y s - eta s) (-alpha (y t) - etaDot t) t := by
    filter_upwards [hdy, hde] with t hdy hde ht
    exact (hdy ht).sub (hde ht)
  have hb : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 < y t - eta t →
      -alpha (y t) - etaDot t ≤ 0 * (y t - eta t) := by
    filter_upwards [hineq] with t hi ht hp
    have ha := hm (show eta t ≤ y t by linarith)
    linarith [hi ht]
  have h := CompleteBarrierAEComparison.genuine_ae_one_sided_invariance
    (fun t => y t - eta t) (fun t => -alpha (y t) - etaDot t)
    a b 0 hab (hy.sub he) hd hb (by linarith)
  intro t ht
  linarith [h t ht]

/-- Every pair of existing absolutely continuous solutions has the same values.
No existence theorem or forward-completeness assumption is hidden in this result. -/
theorem genuine_monotone_ode_uniqueness (y z alpha : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : Monotone alpha)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hz : AbsolutelyContinuousOnInterval z a b)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt y (-alpha (y t)) t)
    (hdz : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt z (-alpha (z t)) t)
    (h0 : y a = z a) : ∀ t ∈ Icc a b, y t = z t := by
  have hyz := genuine_nonlinear_comparison z (fun t => -alpha (z t)) y alpha
    a b hab hm hz hy hdz hdy (Eventually.of_forall fun _ _ => le_rfl) h0.le
  have hzy := genuine_nonlinear_comparison y (fun t => -alpha (y t)) z alpha
    a b hab hm hy hz hdy hdz (Eventually.of_forall fun _ _ => le_rfl) h0.ge
  intro t ht
  exact le_antisymm (hyz t ht) (hzy t ht)

/-- The zero equilibrium cannot be crossed by any existing comparison solution. -/
theorem genuine_comparison_nonnegative (y alpha : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : Monotone alpha) (ha0 : alpha 0 = 0)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt y (-alpha (y t)) t)
    (h0 : 0 ≤ y a) : ∀ t ∈ Icc a b, 0 ≤ y t := by
  have hz : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hdz : ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-alpha 0) t := by
    exact Eventually.of_forall fun t _ => by simpa [ha0] using hasDerivAt_const t (0 : ℝ)
  exact genuine_nonlinear_comparison y (fun t => -alpha (y t))
    (fun _ => 0) alpha a b hab hm hy hz hdy hdz
    (Eventually.of_forall fun _ _ => le_rfl) h0

/-- The nonlinear barrier inequality itself implies safety for every existing
absolutely continuous scalar trajectory. -/
theorem genuine_nonlinear_invariance (eta etaDot alpha : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : Monotone alpha) (ha0 : alpha 0 = 0)
    (he : AbsolutelyContinuousOnInterval eta a b)
    (hde : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt eta (etaDot t) t)
    (hineq : ∀ᵐ t ∂volume, t ∈ Icc a b → -alpha (eta t) ≤ etaDot t)
    (h0 : 0 ≤ eta a) : ∀ t ∈ Icc a b, 0 ≤ eta t := by
  have hz : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hdz : ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-alpha 0) t := by
    exact Eventually.of_forall fun t _ => by simpa [ha0] using hasDerivAt_const t (0 : ℝ)
  exact genuine_nonlinear_comparison eta etaDot (fun _ => 0) alpha
    a b hab hm he hz hde hdz hineq h0

end SafeLearning.CompleteBarrierNonlinearComparison
