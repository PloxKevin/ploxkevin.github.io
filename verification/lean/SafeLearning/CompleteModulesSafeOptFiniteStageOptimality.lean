import SafeLearning.CompleteModulesSafeOptFiniteStageWidth

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteModulesSafeOptFiniteStageOptimality

open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptFiniteStageWidth
open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure

variable {X : Type*} [PseudoMetricSpace X]

/-- A valid finite stopping certificate has an actual attained reachable
maximum, and the actual lower-band report is epsilon optimal against it. -/
theorem actual_finite_safeopt_stopping_certificate_attains_the_true_reachable_benchmark
    (safe : Finset X) (seed : Set X) (f lower upper : X → ℝ) (constant : NNReal)
    (threshold : ℝ) (hs : safe.Nonempty) (hseed_nonempty : seed.Nonempty)
    (hseed : seed ⊆ (safe : Set X))
    (hconfidence : ∀ x ∈ safe, lower x ≤ f x ∧ f x ≤ upper x)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hwidth : actualWidth lower upper (actualFiniteQuery safe lower upper
      (fun x y => constant * dist x y) threshold hs
      (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)) ≤ epsilon)
    (hupdate : actualExpansion (safe : Set X) lower constant threshold ⊆ (safe : Set X)) :
    ∃ optimum : ℝ,
      IsGreatest (f '' actualReachableClosure f constant threshold epsilon seed) optimum ∧
      optimum - f (actualFiniteReport safe lower hs) ≤ epsilon := by
  obtain ⟨hcontains,hoptimal⟩ := actual_finite_safeopt_stopping_certificate_proves_reachable_report_optimality
    safe seed f lower upper constant threshold hs hseed hconfidence epsilon hepsilon hwidth hupdate
  have hfinite : (actualReachableClosure f constant threshold epsilon seed).Finite :=
    safe.finite_toSet.subset hcontains
  have hnonempty : (f '' actualReachableClosure f constant threshold epsilon seed).Nonempty := by
    obtain ⟨x,hx⟩ := hseed_nonempty
    exact ⟨f x,x,mem_iUnion.mpr ⟨0,hx⟩,rfl⟩
  obtain ⟨optimum,hgreatest⟩ := (hfinite.image f).isCompact.exists_isGreatest hnonempty
  refine ⟨optimum,hgreatest,?_⟩
  obtain ⟨x,hx,hvalue⟩ := hgreatest.1
  have h := hoptimal x hx
  rw [hvalue] at h
  linarith

/-- The primitive information and raw-radius hypotheses force a finite-stage
stopping certificate. If the computed lower-band update is unchanged, the
actual report is epsilon optimal against the actual reachable maximum. -/
theorem actual_finite_stage_information_budget_yields_an_actual_epsilon_optimal_reachable_report
    (safe : Finset X) (seed : Set X) (f : X → ℝ) (lower upper : ℕ → X → ℝ)
    (constant : NNReal) (threshold : ℝ) (hs : safe.Nonempty)
    (hseed_nonempty : seed.Nonempty) (hseed : seed ⊆ (safe : Set X))
    (hconfidence : ∀ j x, x ∈ safe → lower j x ≤ f x ∧ f x ≤ upper j x)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x)
    (hupper : ∀ i j, i ≤ j → ∀ x, upper j x ≤ upper i x)
    (sigma : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (multiplier lambda information epsilon : ℝ) (hmultiplier : 0 ≤ multiplier)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon)
    (hradius : ∀ j < N, actualWidth (lower j) (upper j)
      (actualFiniteQuery safe (lower j) (upper j) (fun x y => constant * dist x y) threshold hs
        (fun x hx => (hconfidence j x hx).1.trans (hconfidence j x hx).2)) ≤
          2 * multiplier * sigma j)
    (hsigma : ∀ j < N, (sigma j) ^ 2 ∈ Icc 0 1)
    (hinformation : ∑ j ∈ Finset.range N, Real.log (1 + (sigma j) ^ 2 / lambda) ≤ 2 * information)
    (hbudget : 8 * multiplier ^ 2 * information / Real.log (1 + 1 / lambda) ≤ (N : ℝ) * epsilon ^ 2)
    (hupdate : actualExpansion (safe : Set X) (lower N) constant threshold ⊆ (safe : Set X)) :
    ∃ optimum : ℝ,
      IsGreatest (f '' actualReachableClosure f constant threshold epsilon seed) optimum ∧
      optimum - f (actualFiniteReport safe (lower N) hs) ≤ epsilon := by
  have hwidth := (actual_finite_stage_information_budget_forces_small_query_width_and_report_optimality
    safe f lower upper (fun x y => constant * dist x y) threshold hs hconfidence hlower hupper
    sigma N hN multiplier lambda information epsilon hmultiplier hlambda hepsilon
    hradius hsigma hinformation hbudget).1
  exact actual_finite_safeopt_stopping_certificate_attains_the_true_reachable_benchmark
    safe seed f (lower N) (upper N) constant threshold hs hseed_nonempty hseed
    (hconfidence N) epsilon hepsilon hwidth hupdate

end SafeLearning.CompleteModulesSafeOptFiniteStageOptimality
