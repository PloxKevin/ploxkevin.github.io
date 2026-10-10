import SafeLearning.CompleteModulesLandscapeHalfspaceQP
import SafeLearning.CompleteModulesLandscapeHalfspaceQPInactive
import SafeLearning.CompleteModulesLandscapeControlAffineGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SafeLearning.CompleteModulesLandscapeCBFQP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def inputLie (h : E → ℝ) (g : E → U →L[ℝ] E) (x : E) : StrongDual ℝ U :=
  (fderiv ℝ h x).comp (g x)

def barrierOffset (h : E → ℝ) (f : E → E) (alpha : ℝ → ℝ) (x : E) : ℝ :=
  -alpha (h x) - fderiv ℝ h x (f x)

/-- The controller uses the actual Riesz vector of the input Lie derivative,
not an independently supplied surrogate constraint. -/
def policy (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (alpha : ℝ → ℝ) (nominal : E → U) (x : E) : U :=
  CompleteModulesLandscapeHalfspaceQP.controller
    ((InnerProductSpace.toDual ℝ U).symm (inputLie h g x))
    (nominal x) (barrierOffset h f alpha x)

private theorem actual_Riesz_vector_nonzero (ell : StrongDual ℝ U) (hne : ell ≠ 0) :
    (InnerProductSpace.toDual ℝ U).symm ell ≠ 0 := by
  intro hz
  apply hne
  have he := congrArg (InnerProductSpace.toDual ℝ U) hz
  simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using he

theorem actual_Riesz_halfspace_is_exactly_the_control_affine_barrier_constraint
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (alpha : ℝ → ℝ) (x : E) (v : U) :
    (barrierOffset h f alpha x ≤
      inner ℝ ((InnerProductSpace.toDual ℝ U).symm (inputLie h g x)) v) ↔
    (-alpha (h x) ≤ fderiv ℝ h x (f x) + fderiv ℝ h x (g x v)) := by
  rw [InnerProductSpace.toDual_symm_apply]
  change (-alpha (h x) - fderiv ℝ h x (f x) ≤ fderiv ℝ h x (g x v)) ↔ _
  constructor <;> intro hc <;> linarith

theorem actual_regular_input_Lie_QP_is_feasible_and_the_unique_minimum_change_policy
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (alpha : ℝ → ℝ) (nominal : E → U) (x : E)
    (hregular : inputLie h g x ≠ 0 ∨ barrierOffset h f alpha x ≤ inputLie h g x (nominal x)) :
    (-alpha (h x) ≤ fderiv ℝ h x (f x) +
      fderiv ℝ h x (g x (policy h f g alpha nominal x))) ∧
    ∀ v : U, -alpha (h x) ≤ fderiv ℝ h x (f x) + fderiv ℝ h x (g x v) →
      (‖v - nominal x‖ ^ 2 ≤ ‖policy h f g alpha nominal x - nominal x‖ ^ 2 ↔
        v = policy h f g alpha nominal x) := by
  have hq : (InnerProductSpace.toDual ℝ U).symm (inputLie h g x) ≠ 0 ∨
      barrierOffset h f alpha x ≤ inner ℝ
        ((InnerProductSpace.toDual ℝ U).symm (inputLie h g x)) (nominal x) := by
    rcases hregular with hne | hi
    · exact Or.inl (actual_Riesz_vector_nonzero _ hne)
    · exact Or.inr (by simpa only [InnerProductSpace.toDual_symm_apply] using hi)
  have hp := CompleteModulesLandscapeHalfspaceQPInactive.actual_halfspace_QP_is_feasible_and_unique_when_nondegenerate_or_nominally_feasible
    ((InnerProductSpace.toDual ℝ U).symm (inputLie h g x)) (nominal x)
    (barrierOffset h f alpha x) hq
  refine ⟨(actual_Riesz_halfspace_is_exactly_the_control_affine_barrier_constraint
    h f g alpha x _).mp hp.1, ?_⟩
  intro v hv
  exact hp.2 v ((actual_Riesz_halfspace_is_exactly_the_control_affine_barrier_constraint
    h f g alpha x v).mpr hv)

/-- This theorem states its genuine additional regularity conditions on the
actual input Lie coefficient and offset. Mere C1 h is not promoted to a
locally Lipschitz derivative. -/
theorem actual_CBF_QP_policy_is_locally_lipschitz_from_regular_Lie_data
    (D : Set E) (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (alpha : ℝ → ℝ) (nominal : E → U)
    (hLie : LocallyLipschitzOn D (inputLie h g))
    (hOffset : LocallyLipschitzOn D (barrierOffset h f alpha))
    (hNominal : LocallyLipschitzOn D nominal)
    (hregular : ∀ x ∈ D, inputLie h g x ≠ 0 ∨
      barrierOffset h f alpha x < inputLie h g x (nominal x)) :
    LocallyLipschitzOn D (policy h f g alpha nominal) := by
  have hq : LocallyLipschitzOn D (fun x =>
      (InnerProductSpace.toDual ℝ U).symm (inputLie h g x)) := by
    apply locallyLipschitzOn_iff_restrict.mpr
    exact (InnerProductSpace.toDual ℝ U).symm.lipschitz.locallyLipschitz.comp hLie.restrict
  exact CompleteModulesLandscapeHalfspaceQPInactive.actual_halfspace_QP_is_locally_lipschitz_with_nondegenerate_or_strictly_inactive_constraints
    D _ nominal (barrierOffset h f alpha) hq hNominal hOffset
    (fun x hx => by
      rcases hregular x hx with hne | hi
      · exact Or.inl (actual_Riesz_vector_nonzero _ hne)
      · exact Or.inr (by simpa only [InnerProductSpace.toDual_symm_apply] using hi))

/-- From every safe initial state, the actual minimum-change CBF-QP produces
a global safe closed-loop path under the explicit compactness and coefficient
regularity conditions. Existence and safety are constructed, not assumed. -/
theorem actual_regular_CBF_QP_on_a_compact_safe_set_has_a_global_safe_solution
    [FiniteDimensional ℝ E]
    (D : Set E) (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E)
    (alpha : ℝ → ℝ) (nominal : E → U) (J : Set ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D)
    (hf : LocallyLipschitzOn D f) (hg : LocallyLipschitzOn D g)
    (hLie : LocallyLipschitzOn D (inputLie h g))
    (hOffset : LocallyLipschitzOn D (barrierOffset h f alpha))
    (hNominal : LocallyLipschitzOn D nominal)
    (hregular : ∀ x ∈ D, inputLie h g x ≠ 0 ∨
      barrierOffset h f alpha x < inputLie h g x (nominal x))
    (hm : MonotoneOn alpha J) (ha0 : alpha 0 = 0) (hJ0 : (0 : ℝ) ∈ J)
    (hhJ : MapsTo h D J) (hcompact : IsCompact {x | 0 ≤ h x})
    (hsubset : {x | 0 ≤ h x} ⊆ D) (x₀ : E) (hx₀ : 0 ≤ h x₀) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ≥ 0, 0 ≤ h (x t)) ∧
      (∀ t ≥ 0, HasDerivWithinAt x
        (f (x t) + g (x t) (policy h f g alpha nominal (x t))) (Ici 0) t) ∧
      ∀ t > 0, HasDerivAt x
        (f (x t) + g (x t) (policy h f g alpha nominal (x t))) t := by
  apply CompleteModulesLandscapeControlAffineGlobal.actual_compact_control_affine_barrier_and_locally_lipschitz_policy_have_a_global_safe_solution
    D f g (policy h f g alpha nominal) hf hg
    (actual_CBF_QP_policy_is_locally_lipschitz_from_regular_Lie_data
      D h f g alpha nominal hLie hOffset hNominal hregular)
    hD h alpha J hh hm ha0 hJ0 hhJ
    (fun z hz => (actual_regular_input_Lie_QP_is_feasible_and_the_unique_minimum_change_policy
      h f g alpha nominal z ((hregular z hz).imp_right le_of_lt)).1) hcompact hsubset x₀ hx₀

end SafeLearning.CompleteModulesLandscapeCBFQP
