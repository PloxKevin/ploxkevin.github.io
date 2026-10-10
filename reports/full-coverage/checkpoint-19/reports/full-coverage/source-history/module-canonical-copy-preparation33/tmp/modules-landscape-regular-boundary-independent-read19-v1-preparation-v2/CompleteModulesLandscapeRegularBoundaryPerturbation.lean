import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeRegularBoundaryPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero boundary differential gives an actual constant inward direction. -/
theorem actual_nonzero_boundary_differential_has_a_positive_constant_direction
    (h : E → ℝ) (x₀ : E) (hregular : fderiv ℝ h x₀ ≠ 0) :
    ∃ v : E, 0 < fderiv ℝ h x₀ v := by
  classical
  have hex : ∃ v : E, fderiv ℝ h x₀ v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hregular
    ext v
    simpa using hn v
  obtain ⟨v,hv⟩ := hex
  rcases lt_or_gt_of_ne hv with hv | hv
  · refine ⟨-v,?_⟩
    simpa only [map_neg] using neg_pos.mpr hv
  · exact ⟨v,hv⟩

/-- C1 regularity and the weak boundary-only inequality produce a locally
strict boundary inequality for F+epsilon*v. The perturbation direction is
constant; no Lipschitz derivative of h or C1 field F is assumed. -/
theorem actual_regular_boundary_has_a_locally_strict_constant_inward_perturbation
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hh : ContDiffOn ℝ 1 h D) (x₀ : E) (hx₀ : x₀ ∈ D)
    (hregular : fderiv ℝ h x₀ ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z)) :
    ∃ v : E, ∃ r > (0 : ℝ), ball x₀ r ⊆ D ∧
      (∀ z ∈ ball x₀ r, 0 < fderiv ℝ h z v) ∧
      ∀ ε > (0 : ℝ), ∀ z ∈ ball x₀ r, h z = 0 →
        0 < fderiv ℝ h z (F z + ε • v) := by
  obtain ⟨v,hv⟩ := actual_nonzero_boundary_differential_has_a_positive_constant_direction h x₀ hregular
  have hgrad : ContinuousAt (fderiv ℝ h) x₀ :=
    (hh.contDiffAt (hD.mem_nhds hx₀)).continuousAt_fderiv (by norm_num)
  have hdir : ContinuousAt (fun z => fderiv ℝ h z v) x₀ := hgrad.clm_apply continuousAt_const
  have hpositive : {z : E | 0 < fderiv ℝ h z v} ∈ 𝓝 x₀ :=
    hdir.preimage_mem_nhds (Ioi_mem_nhds hv)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds hx₀) hpositive)
  refine ⟨v,r,hr,fun z hz => (hball hz).1,fun z hz => (hball hz).2,?_⟩
  intro ε hε z hz hzero
  have hweak := hinward z (hball hz).1 hzero
  have hstrict : 0 < fderiv ℝ h z v := (hball hz).2
  rw [map_add,map_smul]
  change 0 < fderiv ℝ h z (F z) + ε * fderiv ℝ h z v
  exact add_pos_of_nonneg_of_pos hweak (mul_pos hε hstrict)

/-- Strict positive derivative at each zero fences a true scalar path above
zero. Strictness is essential here; the weak condition alone is insufficient. -/
theorem actual_strict_boundary_derivative_keeps_a_scalar_path_nonnegative
    (g d : ℝ → ℝ) (a b : ℝ) (hg : ContinuousOn g (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt g (d t) (Ici t) t)
    (hinit : 0 ≤ g a) (hstrict : ∀ t ∈ Ico a b, g t = 0 → 0 < d t) :
    ∀ t ∈ Icc a b, 0 ≤ g t := by
  have hfence : ∀ t ∈ Icc a b, -g t ≤ (0 : ℝ) := by
    apply image_le_of_deriv_right_lt_deriv_boundary hg.neg
      (fun t ht => (hderiv t ht).neg) (neg_nonpos.mpr hinit)
      (fun t => hasDerivAt_const t (0 : ℝ))
    intro t ht heq
    have hzero : g t = 0 := neg_eq_zero.mp heq
    exact neg_neg_of_pos (hstrict t ht hzero)
  intro t ht
  exact neg_nonpos.mp (hfence t ht)

/-- A true vector ODE path with a strictly inward boundary-only condition
stays in the superlevel set on its existing interval. This is the strict
component used for the constant perturbations, rather than a weak Nagumo claim. -/
theorem actual_strict_boundary_vector_ode_path_stays_in_the_superlevel_set
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hh : ContDiffOn ℝ 1 h D) (x : ℝ → E) (a b : ℝ)
    (hx : ContinuousOn x (Icc a b)) (hxD : MapsTo x (Icc a b) D)
    (hODE : ∀ t ∈ Ico a b, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hinit : 0 ≤ h (x a))
    (hstrict : ∀ z ∈ D, h z = 0 → 0 < fderiv ℝ h z (F z)) :
    ∀ t ∈ Icc a b, 0 ≤ h (x t) := by
  refine actual_strict_boundary_derivative_keeps_a_scalar_path_nonnegative
    (fun t => h (x t)) (fun t => fderiv ℝ h (x t) (F (x t))) a b
    (hh.continuousOn.comp hx hxD) ?_ hinit ?_
  · intro t ht
    exact ((hh.differentiableOn (by norm_num)).differentiableAt
      (hD.mem_nhds (hxD (Ico_subset_Icc_self ht)))).hasFDerivAt.comp_hasDerivWithinAt t (hODE t ht)
  · intro t ht hzero
    exact hstrict (x t) (hxD (Ico_subset_Icc_self ht)) hzero

end SafeLearning.CompleteModulesLandscapeRegularBoundaryPerturbation
