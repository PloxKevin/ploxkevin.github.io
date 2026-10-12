import SafeLearning.CompleteModulesLandscapeMaximalExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeGlobalExistence

open SafeLearning.CompleteModulesLandscapeMaximalEndpoint
open SafeLearning.CompleteModulesLandscapeMaximalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual invariance is a statement about true forward ODE solutions from C.
It does not assert that any solution exists, or that its endpoint is infinite. -/
def IsForwardInvariant (f : E → E) (D C : Set E) : Prop :=
  ∀ x₀ ∈ C, ∀ p : ForwardSolution f D x₀,
    MapsTo p.path (forwardTimeDomain p.endpoint) C

variable [FiniteDimensional ℝ E]

/-- A compact invariant subset of the open domain of a locally Lipschitz field
has an actual global forward solution from each initial state in that set.
Maximal existence and infinite forward lifetime are both derived. -/
theorem actual_compact_invariant_set_yields_global_forward_solution_existence
    (f : E → E) (D C : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hC : IsCompact C) (hCD : C ⊆ D) (hinvariant : IsForwardInvariant f D C)
    (x₀ : E) (hx₀ : x₀ ∈ C) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ MapsTo x (Ici 0) C ∧
      (∀ t ∈ Ici 0, HasDerivWithinAt x (f (x t)) (Ici 0) t) ∧
      (∀ t ∈ Ioi 0, HasDerivAt x (f (x t)) t) := by
  obtain ⟨B,hB,x,hinit,hxD,hODE,hmax⟩ :=
    actual_locally_lipschitz_field_has_a_forward_maximal_solution_from_every_domain_point
      f D hD hf x₀ (hCD hx₀)
  let p : ForwardSolution f D x₀ := ⟨B,hB,x,hinit,hxD,hODE⟩
  have hxC : MapsTo x (forwardTimeDomain B) C := hinvariant x₀ hx₀ p
  obtain ⟨htop,htrap,hglobal,hpositive⟩ :=
    actual_provided_maximal_compact_trapped_solution_solves_the_ode_at_all_forward_times
      f D C hD hf hC hCD x B hB hxC hODE hmax
  exact ⟨x,hinit,htrap,hglobal,hpositive⟩

/-- If every domain point lies in some compact invariant subset of the domain,
then every domain point admits an actual global forward ODE solution. -/
theorem actual_compact_invariant_sets_covering_the_domain_yield_global_forward_existence
    (f : E → E) (D : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hcover : ∀ x₀ ∈ D, ∃ C : Set E,
      IsCompact C ∧ C ⊆ D ∧ x₀ ∈ C ∧ IsForwardInvariant f D C) :
    ∀ x₀ ∈ D, ∃ x : ℝ → E, x 0 = x₀ ∧ MapsTo x (Ici 0) D ∧
      (∀ t ∈ Ici 0, HasDerivWithinAt x (f (x t)) (Ici 0) t) ∧
      (∀ t ∈ Ioi 0, HasDerivAt x (f (x t)) t) := by
  intro x₀ hx₀
  obtain ⟨C,hC,hCD,hxC,hinvariant⟩ := hcover x₀ hx₀
  obtain ⟨x,hinit,htrap,hglobal,hpositive⟩ :=
    actual_compact_invariant_set_yields_global_forward_solution_existence
      f D C hD hf hC hCD hinvariant x₀ hxC
  exact ⟨x,hinit,htrap.mono_right hCD,hglobal,hpositive⟩

end SafeLearning.CompleteModulesLandscapeGlobalExistence
