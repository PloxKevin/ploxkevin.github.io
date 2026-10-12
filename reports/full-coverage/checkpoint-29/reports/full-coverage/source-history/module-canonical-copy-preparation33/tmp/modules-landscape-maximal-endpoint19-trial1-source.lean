import SafeLearning.CompleteModulesLandscapeCompactContinuation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeMaximalEndpoint

/-- The forward domain with an extended-real upper endpoint. -/
def forwardTimeDomain (B : EReal) : Set ℝ :=
  {t | 0 ≤ t ∧ (t : EReal) < B}

@[simp] theorem forwardTimeDomain_coe (T : ℝ) :
    forwardTimeDomain (T : EReal) = Ico 0 T := by
  ext t
  simp only [forwardTimeDomain, mem_setOf_eq, EReal.coe_lt_coe_iff, mem_Ico]

@[simp] theorem forwardTimeDomain_top :
    forwardTimeDomain ⊤ = Ici 0 := by
  ext t
  simp only [forwardTimeDomain, mem_setOf_eq, EReal.coe_lt_top, and_true, mem_Ici]

theorem forwardTimeDomain_mono {B B' : EReal} (h : B ≤ B') :
    forwardTimeDomain B ⊆ forwardTimeDomain B' := by
  intro t ht
  exact ⟨ht.1,ht.2.trans_le h⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward maximality forbids any longer real-time solution in D that agrees
with the entire old trajectory. It does not assume forward completeness. -/
def IsForwardMaximal (f : E → E) (D : Set E) (x : ℝ → E) (B : EReal) : Prop :=
  ∀ S : ℝ, B < (S : EReal) →
    ¬ ∃ y : ℝ → E, EqOn x y (forwardTimeDomain B) ∧
      MapsTo y (Ico 0 S) D ∧
      ∀ t ∈ Ico 0 S, HasDerivWithinAt y (f (y t)) (Ico 0 S) t

variable [FiniteDimensional ℝ E]

/-- For a provided maximal solution, compact trapping excludes every finite
positive endpoint. The proof uses the actual finite-time continuation theorem.
Existence of maximal solutions for all initial states is a separate theorem. -/
theorem actual_provided_maximal_compact_trapped_solution_has_infinite_forward_endpoint
    (f : E → E) (D C : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hC : IsCompact C) (hCD : C ⊆ D) (x : ℝ → E) (B : EReal) (hB : 0 < B)
    (hxC : MapsTo x (forwardTimeDomain B) C)
    (hODE : ∀ t ∈ forwardTimeDomain B,
      HasDerivWithinAt x (f (x t)) (forwardTimeDomain B) t)
    (hmax : IsForwardMaximal f D x B) : B = ⊤ := by
  by_contra hfinite
  let T : ℝ := B.toReal
  have hT : 0 < T := EReal.toReal_pos hB hfinite
  have hTB : (T : EReal) = B := EReal.coe_toReal hfinite (ne_bot_of_gt hB)
  have hdomain : forwardTimeDomain B = Ico 0 T := by
    rw [← hTB,forwardTimeDomain_coe]
  have hxC' : MapsTo x (Ico 0 T) C := by simpa only [hdomain] using hxC
  have hODE' : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt x (f (x t)) (Ico 0 T) t := by
    simpa only [hdomain] using hODE
  obtain ⟨ε,hε,y,hEq,hyC,hlim,hyD,hyODE,hyinterior⟩ :=
    SafeLearning.CompleteModulesLandscapeCompactContinuation.actual_compact_trapped_solution_of_a_locally_lipschitz_field_continues_past_finite_time
      f D C hD hf hC hCD x T hT hxC' hODE'
  have hlong : B < ((T + ε : ℝ) : EReal) := by
    rw [← hTB]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  apply hmax (T + ε) hlong
  refine ⟨y,?_,hyD,hyODE⟩
  simpa only [hdomain] using hEq

/-- The same provided maximal solution is therefore an actual ODE solution on
all nonnegative times, with its compact trapping preserved. This conclusion
is derived, rather than supplied as a forward-completeness assumption. -/
theorem actual_provided_maximal_compact_trapped_solution_solves_the_ode_at_all_forward_times
    (f : E → E) (D C : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (hC : IsCompact C) (hCD : C ⊆ D) (x : ℝ → E) (B : EReal) (hB : 0 < B)
    (hxC : MapsTo x (forwardTimeDomain B) C)
    (hODE : ∀ t ∈ forwardTimeDomain B,
      HasDerivWithinAt x (f (x t)) (forwardTimeDomain B) t)
    (hmax : IsForwardMaximal f D x B) :
    B = ⊤ ∧ MapsTo x (Ici 0) C ∧
      (∀ t ∈ Ici 0, HasDerivWithinAt x (f (x t)) (Ici 0) t) ∧
      (∀ t ∈ Ioi 0, HasDerivAt x (f (x t)) t) := by
  have htop := actual_provided_maximal_compact_trapped_solution_has_infinite_forward_endpoint
    f D C hD hf hC hCD x B hB hxC hODE hmax
  have hdomain : forwardTimeDomain B = Ici 0 := by rw [htop,forwardTimeDomain_top]
  have hglobal : ∀ t ∈ Ici 0, HasDerivWithinAt x (f (x t)) (Ici 0) t := by
    simpa only [hdomain] using hODE
  refine ⟨htop,?_,hglobal,?_⟩
  · simpa only [hdomain] using hxC
  · intro t ht
    exact (hglobal t ht.le).hasDerivAt (Ici_mem_nhds ht)

end SafeLearning.CompleteModulesLandscapeMaximalEndpoint
