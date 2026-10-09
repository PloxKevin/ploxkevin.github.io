import SafeLearning.CompleteBarrierAbsolutelyContinuous
import SafeLearning.CompleteBarrierNonlinearComparison

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteBarrierVectorChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C1 barrier on an open domain preserves absolute continuity of any
trajectory that remains in that domain. Compactness supplies a uniform
Lipschitz constant only on this trajectory's image. -/
theorem genuine_c1_ac_composition (h : E → ℝ) (x : ℝ → E) (D : Set E) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hx : AbsolutelyContinuousOnInterval x a b) (hxD : MapsTo x (uIcc a b) D) :
    AbsolutelyContinuousOnInterval (h ∘ x) a b := by
  let K : Set E := x '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hx.continuousOn
  have hloc : LocallyLipschitzOn K h := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hhx : ContDiffAt ℝ 1 h (x t) :=
      (hh (x t) (hxD ht)).contDiffAt (hD.mem_nhds (hxD ht))
    obtain ⟨L, U, hU, hL⟩ := hhx.exists_lipschitzOnWith
    exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  exact hL.comp_absolutelyContinuousOnInterval
    (fun t ht => ⟨t, ht, rfl⟩) hx

/-- Actual almost-everywhere vector derivatives give the Lie-derivative chain
rule. The derivative of h is taken from C1 regularity on its stated domain. -/
theorem genuine_ae_vector_chain_rule (h : E → ℝ) (x velocity : ℝ → E)
    (D : Set E) (a b : ℝ) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hab : a ≤ b) (hxD : MapsTo x (uIcc a b) D)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt x (velocity t) t) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      HasDerivAt (h ∘ x) (fderiv ℝ h (x t) (velocity t)) t := by
  filter_upwards [hd] with t hd ht
  have ht' : t ∈ uIcc a b := by simpa [uIcc_of_le hab] using ht
  have hhx : ContDiffAt ℝ 1 h (x t) :=
    (hh (x t) (hxD ht')).contDiffAt (hD.mem_nhds (hxD ht'))
  exact (hhx.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t (hd ht)

/-- The linear exponential bound for the actual vector trajectory, including
measurable closed loops whenever a Caratheodory solution exists. -/
theorem genuine_vector_exponential_barrier (h : E → ℝ) (x velocity : ℝ → E)
    (D : Set E) (beta horizon : ℝ) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hT : 0 ≤ horizon) (hx : AbsolutelyContinuousOnInterval x 0 horizon)
    (hxD : MapsTo x (uIcc 0 horizon) D)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 horizon → HasDerivAt x (velocity t) t)
    (hb : ∀ᵐ t ∂volume, t ∈ Icc 0 horizon →
      -beta * h (x t) ≤ fderiv ℝ h (x t) (velocity t)) :
    ∀ t ∈ Icc 0 horizon, h (x 0) * Real.exp (-beta * t) ≤ h (x t) := by
  intro t ht
  exact CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
    (h ∘ x) (fun t => fderiv ℝ h (x t) (velocity t)) beta horizon hT
    (genuine_c1_ac_composition h x D 0 horizon hD hh hx hxD)
    (genuine_ae_vector_chain_rule h x velocity D 0 horizon hD hh hT hxD hd)
    hb t ht

theorem genuine_vector_linear_invariance (h : E → ℝ) (x velocity : ℝ → E)
    (D : Set E) (beta horizon : ℝ) (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hT : 0 ≤ horizon) (hx : AbsolutelyContinuousOnInterval x 0 horizon)
    (hxD : MapsTo x (uIcc 0 horizon) D)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 horizon → HasDerivAt x (velocity t) t)
    (hb : ∀ᵐ t ∂volume, t ∈ Icc 0 horizon →
      -beta * h (x t) ≤ fderiv ℝ h (x t) (velocity t))
    (h0 : 0 ≤ h (x 0)) : ∀ t ∈ Icc 0 horizon, 0 ≤ h (x t) := by
  intro t ht
  exact (mul_nonneg h0 (Real.exp_pos _).le).trans
    (genuine_vector_exponential_barrier h x velocity D beta horizon hD hh hT hx hxD hd hb t ht)

/-- The nonlinear version uses monotonicity of alpha instead of a time-only
exponential factor, on the actual vector trajectory. -/
theorem genuine_vector_nonlinear_invariance (h : E → ℝ) (x velocity : ℝ → E)
    (alpha : ℝ → ℝ) (D : Set E) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hab : a ≤ b)
    (hm : Monotone alpha) (ha0 : alpha 0 = 0)
    (hx : AbsolutelyContinuousOnInterval x a b) (hxD : MapsTo x (uIcc a b) D)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt x (velocity t) t)
    (hb : ∀ᵐ t ∂volume, t ∈ Icc a b →
      -alpha (h (x t)) ≤ fderiv ℝ h (x t) (velocity t))
    (h0 : 0 ≤ h (x a)) : ∀ t ∈ Icc a b, 0 ≤ h (x t) := by
  exact CompleteBarrierNonlinearComparison.genuine_nonlinear_invariance
    (h ∘ x) (fun t => fderiv ℝ h (x t) (velocity t)) alpha a b hab hm ha0
    (genuine_c1_ac_composition h x D a b hD hh hx hxD)
    (genuine_ae_vector_chain_rule h x velocity D a b hD hh hab hxD hd) hb h0

end SafeLearning.CompleteBarrierVectorChainRule
