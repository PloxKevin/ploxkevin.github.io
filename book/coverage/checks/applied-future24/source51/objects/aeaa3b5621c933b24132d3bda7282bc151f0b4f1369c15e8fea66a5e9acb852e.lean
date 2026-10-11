import SafeLearning.CompleteModulesLandscapeBarrierGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteModulesLandscapeControlAffineGlobal

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Applying a locally Lipschitz operator-valued function to a locally
Lipschitz input is locally Lipschitz. The bilinear evaluation map is C1. -/
theorem actual_locally_lipschitz_control_operator_applied_to_a_locally_lipschitz_policy_is_locally_lipschitz
    (D : Set E) (g : E → U →L[ℝ] E) (u : E → U)
    (hg : LocallyLipschitzOn D g) (hu : LocallyLipschitzOn D u) :
    LocallyLipschitzOn D (fun z => g z (u z)) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  have hdiff : ContDiff ℝ 1 (fun p : (U →L[ℝ] E) × U => p.1 p.2) :=
    isBoundedBilinearMap_apply.contDiff
  have happ : LocallyLipschitz (fun p : (U →L[ℝ] E) × U => p.1 p.2) :=
    hdiff.locallyLipschitz
  exact happ.comp (hg.restrict.prodMk hu.restrict)

/-- The source's component regularity assumptions derive local Lipschitz
regularity of the actual deployed control-affine field. -/
theorem actual_locally_lipschitz_control_affine_components_and_policy_give_a_locally_lipschitz_closed_loop
    (D : Set E) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U)
    (hf : LocallyLipschitzOn D f) (hg : LocallyLipschitzOn D g)
    (hu : LocallyLipschitzOn D u) :
    LocallyLipschitzOn D (fun z => f z + g z (u z)) := by
  exact hf.add
    (actual_locally_lipschitz_control_operator_applied_to_a_locally_lipschitz_policy_is_locally_lipschitz
      D g u hg hu)

/-- For a compact safe superlevel set inside an open domain, the actual C1
control-affine barrier inequality and source regularity assumptions yield a
global safe solution from every safe initial state. -/
theorem actual_compact_control_affine_barrier_and_locally_lipschitz_policy_have_a_global_safe_solution
    [FiniteDimensional ℝ E]
    (D : Set E) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U)
    (hf : LocallyLipschitzOn D f) (hg : LocallyLipschitzOn D g)
    (hu : LocallyLipschitzOn D u) (hD : IsOpen D)
    (h : E → ℝ) (alpha : ℝ → ℝ) (J : Set ℝ)
    (hh : ContDiffOn ℝ 1 h D) (hm : MonotoneOn alpha J)
    (ha0 : alpha 0 = 0) (hJ0 : (0 : ℝ) ∈ J) (hhJ : MapsTo h D J)
    (hbarrier : ∀ z ∈ D,
      -alpha (h z) ≤ fderiv ℝ h z (f z) + fderiv ℝ h z (g z (u z)))
    (hcompact : IsCompact {z | 0 ≤ h z}) (hsubset : {z | 0 ≤ h z} ⊆ D)
    (x₀ : E) (hx₀ : 0 ≤ h x₀) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ≥ 0, 0 ≤ h (x t)) ∧
      (∀ t ≥ 0, HasDerivWithinAt x (f (x t) + g (x t) (u (x t))) (Ici 0) t) ∧
      (∀ t > 0, HasDerivAt x (f (x t) + g (x t) (u (x t))) t) := by
  apply SafeLearning.CompleteModulesLandscapeBarrierGlobal.actual_compact_barrier_superlevel_set_has_a_global_safe_solution_from_every_safe_state
    (fun z => f z + g z (u z)) D h alpha J hD
    (actual_locally_lipschitz_control_affine_components_and_policy_give_a_locally_lipschitz_closed_loop
      D f g u hf hg hu) hh hm ha0 hJ0 hhJ
    (fun z hz => ?_) hcompact hsubset x₀ hx₀
  rw [map_add]
  exact hbarrier z hz

end SafeLearning.CompleteModulesLandscapeControlAffineGlobal
