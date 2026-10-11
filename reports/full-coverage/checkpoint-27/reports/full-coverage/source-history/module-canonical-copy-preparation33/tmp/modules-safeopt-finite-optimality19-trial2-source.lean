import SafeLearning.CompleteModulesSafeOptConfidenceIntersections
import SafeLearning.CompleteModulesSafeOptReachableClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteModulesSafeOptFiniteOptimality

open SafeLearning.CompleteModulesSafeOptConfidenceIntersections
open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure

variable {X : Type*} [DecidableEq X]

def actualWidth (lower upper : X → ℝ) (x : X) : ℝ := upper x - lower x

/-- The actual finite candidate union uses the existing source-faithful
optimistic expander and potential-maximizer definitions. -/
def actualFiniteCandidates (safe : Finset X) (lower upper : X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) : Finset X := by
  classical
  exact safe.filter (fun x => x ∈ actualExpanders (safe : Set X) upper cost threshold ∪
    actualMaximizers (safe : Set X) lower upper)

/-- A finite nonempty safe set supplies an actual lower-bound maximizer. -/
def actualFiniteReport (safe : Finset X) (lower : X → ℝ) (hs : safe.Nonempty) : X :=
  Classical.choose (Finset.exists_max_image safe lower hs)

omit [DecidableEq X] in
theorem actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band
    (safe : Finset X) (lower : X → ℝ) (hs : safe.Nonempty) :
    actualFiniteReport safe lower hs ∈ safe ∧
      ∀ x ∈ safe, lower x ≤ lower (actualFiniteReport safe lower hs) :=
  Classical.choose_spec (Finset.exists_max_image safe lower hs)

/-- Well-formed confidence bands make the actual report a potential maximizer,
so the finite acquisition set is genuinely nonempty. -/
theorem actual_finite_candidate_union_is_nonempty
    (safe : Finset X) (lower upper : X → ℝ) (cost : X → X → ℝ) (threshold : ℝ)
    (hs : safe.Nonempty) (hbands : ∀ x ∈ safe, lower x ≤ upper x) :
    (actualFiniteCandidates safe lower upper cost threshold).Nonempty := by
  obtain ⟨hr,hmax⟩ := actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band safe lower hs
  refine ⟨actualFiniteReport safe lower hs,?_⟩
  simp only [actualFiniteCandidates,Finset.mem_filter]
  exact ⟨hr,Or.inr ⟨hr,fun y hy => (hmax y hy).trans (hbands _ hr)⟩⟩

/-- The query is constructed by a genuine finite maximum of interval width. -/
def actualFiniteQuery (safe : Finset X) (lower upper : X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) (hs : safe.Nonempty)
    (hbands : ∀ x ∈ safe, lower x ≤ upper x) : X :=
  Classical.choose (Finset.exists_max_image
    (actualFiniteCandidates safe lower upper cost threshold) (actualWidth lower upper)
    (actual_finite_candidate_union_is_nonempty safe lower upper cost threshold hs hbands))

theorem actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    (safe : Finset X) (lower upper : X → ℝ) (cost : X → X → ℝ) (threshold : ℝ)
    (hs : safe.Nonempty) (hbands : ∀ x ∈ safe, lower x ≤ upper x) :
    actualFiniteQuery safe lower upper cost threshold hs hbands ∈
      actualFiniteCandidates safe lower upper cost threshold ∧
    ∀ x ∈ actualFiniteCandidates safe lower upper cost threshold,
      actualWidth lower upper x ≤
        actualWidth lower upper (actualFiniteQuery safe lower upper cost threshold hs hbands) :=
  Classical.choose_spec (Finset.exists_max_image
    (actualFiniteCandidates safe lower upper cost threshold) (actualWidth lower upper)
    (actual_finite_candidate_union_is_nonempty safe lower upper cost threshold hs hbands))

/-- On valid actual bands, a small width at the actual acquisition maximizer
certifies the actual pessimistic report against every certified design point. -/
theorem actual_query_width_bound_certifies_the_actual_report_on_the_finite_safe_set
    (safe : Finset X) (f lower upper : X → ℝ) (cost : X → X → ℝ) (threshold : ℝ)
    (hs : safe.Nonempty) (hconfidence : ∀ x ∈ safe, lower x ≤ f x ∧ f x ≤ upper x)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hwidth : actualWidth lower upper (actualFiniteQuery safe lower upper cost threshold hs
      (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)) ≤ epsilon) :
    ∀ x ∈ safe, f x ≤ f (actualFiniteReport safe lower hs) + epsilon := by
  obtain ⟨hr,hreport⟩ := actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band safe lower hs
  obtain ⟨_,hquery⟩ := actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    safe lower upper cost threshold hs (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)
  intro x hx
  by_cases hm : x ∈ actualMaximizers (safe : Set X) lower upper
  · have hc : x ∈ actualFiniteCandidates safe lower upper cost threshold := by
      simp only [actualFiniteCandidates,Finset.mem_filter]
      exact ⟨hx,Or.inr hm⟩
    have hw := (hquery x hc).trans hwidth
    have hl := hreport x hx
    have hfr := (hconfidence _ hr).1
    have hfx := (hconfidence x hx).2
    dsimp only [actualWidth] at hw
    linarith
  · have hnot : ¬ ∀ y ∈ safe, lower y ≤ upper x := by
      intro hy
      exact hm ⟨hx,hy⟩
    push Not at hnot
    obtain ⟨y,hy,hyl⟩ := hnot
    have hly := hreport y hy
    have hfr := (hconfidence _ hr).1
    have hfx := (hconfidence x hx).2
    linarith

variable [PseudoMetricSpace X]

/-- A computed safe update with no pending lower-band certificates and narrow
optimistic expanders contains the actual epsilon-reachable closure of its seed.
The reachable-set inclusion is derived, rather than assumed as optimality data. -/
omit [DecidableEq X] in
theorem actual_unchanged_lower_band_update_and_narrow_expanders_contains_the_reachable_closure
    (safe seed : Set X) (f lower upper : X → ℝ) (constant : NNReal)
    (threshold epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hseed : seed ⊆ safe)
    (hupper : ∀ x ∈ safe, f x ≤ upper x)
    (hnarrow : ∀ x ∈ actualExpanders safe upper (fun x y => constant * dist x y) threshold,
      actualWidth lower upper x ≤ epsilon)
    (hupdate : actualExpansion safe lower constant threshold ⊆ safe) :
    actualReachableClosure f constant threshold epsilon seed ⊆ safe := by
  have hreach : actualReach f constant threshold epsilon safe ⊆ safe := by
    intro y hy
    rcases hy with hy | ⟨x,hx,hcert⟩
    · exact hy
    · by_contra hyn
      have hg : x ∈ actualExpanders safe upper (fun x y => constant * dist x y) threshold := by
        refine ⟨hx,y,hyn,?_⟩
        have hu := hupper x hx
        linarith
      have hw := hnarrow x hg
      have hu := hupper x hx
      have hlower : threshold ≤ lower x - constant * dist x y := by
        dsimp only [actualWidth] at hw
        linarith
      exact hyn (hupdate ⟨x,hx,hlower⟩)
  have hiter : ∀ n, actualReachIterates f constant threshold epsilon seed n ⊆ safe := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      exact ((actual_reach_operator_keeps_every_old_point_and_is_monotone
        f constant threshold epsilon).2 ih).trans hreach
  intro x hx
  obtain ⟨n,hn⟩ := mem_iUnion.mp hx
  exact hiter n hn

/-- The actual finite SafeOpt stopping certificate proves epsilon optimality
on the true epsilon-reachable set, using the same report and query definitions. -/
theorem actual_finite_safeopt_stopping_certificate_proves_reachable_report_optimality
    (safe : Finset X) (seed : Set X) (f lower upper : X → ℝ) (constant : NNReal)
    (threshold : ℝ) (hs : safe.Nonempty)
    (hseed : seed ⊆ (safe : Set X))
    (hconfidence : ∀ x ∈ safe, lower x ≤ f x ∧ f x ≤ upper x)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hwidth : actualWidth lower upper (actualFiniteQuery safe lower upper
      (fun x y => constant * dist x y) threshold hs
      (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)) ≤ epsilon)
    (hupdate : actualExpansion (safe : Set X) lower constant threshold ⊆ (safe : Set X)) :
    actualReachableClosure f constant threshold epsilon seed ⊆ (safe : Set X) ∧
      ∀ x ∈ actualReachableClosure f constant threshold epsilon seed,
        f x ≤ f (actualFiniteReport safe lower hs) + epsilon := by
  have hquery := (actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    safe lower upper (fun x y => constant * dist x y) threshold hs
    (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)).2
  have hnarrow : ∀ x ∈ actualExpanders (safe : Set X) upper (fun x y => constant * dist x y) threshold,
      actualWidth lower upper x ≤ epsilon := by
    intro x hx
    apply (hquery x ?_).trans hwidth
    simp only [actualFiniteCandidates,Finset.mem_filter]
    exact ⟨hx.1,Or.inl hx⟩
  have hcontains := actual_unchanged_lower_band_update_and_narrow_expanders_contains_the_reachable_closure
    (safe : Set X) seed f lower upper constant threshold epsilon hepsilon hseed
    (fun x hx => (hconfidence x hx).2) hnarrow hupdate
  exact ⟨hcontains,fun x hx =>
    actual_query_width_bound_certifies_the_actual_report_on_the_finite_safe_set
      safe f lower upper (fun x y => constant * dist x y) threshold hs hconfidence
      epsilon hepsilon hwidth x (hcontains hx)⟩

end SafeLearning.CompleteModulesSafeOptFiniteOptimality
