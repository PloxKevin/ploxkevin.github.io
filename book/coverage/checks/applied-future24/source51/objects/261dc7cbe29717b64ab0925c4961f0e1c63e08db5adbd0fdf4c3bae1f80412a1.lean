import SafeLearning.CompleteModulesSafeOptReachableClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptDisconnectedConsequences
open CompleteModulesSafeOptPracticeTheorems CompleteModulesSafeOptReachableClosure

theorem actual_design_domain_valid_cone_cannot_cross_an_unsafe_design_point
    (design : Set ℝ) (f : design → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold lower : ℝ)
    (anchor barrier candidate : design) (hlower : lower ≤ f anchor)
    (hunsafe : f barrier < threshold) (hleft : (anchor : ℝ) < barrier)
    (hright : (barrier : ℝ) ≤ candidate) :
    ¬ threshold ≤ lower - constant * dist anchor candidate := by
  have hd : dist anchor barrier ≤ dist anchor candidate := by
    simp only [Subtype.dist_eq, Real.dist_eq]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  have ht := actual_metric_lipschitz_lower_confidence_transfer f constant hf
    anchor barrier lower hlower
  have hc := mul_le_mul_of_nonneg_left hd constant.coe_nonneg
  intro hcert
  linarith

theorem actual_design_domain_confidence_rounds_never_cross_the_unsafe_hole
    (design : Set ℝ) (f : design → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold : ℝ) (barrier : design)
    (hunsafe : f barrier < threshold) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x : ℝ) < barrier) (lower : ℕ → design → ℝ)
    (hconfidence : ∀ n x, lower n x ≤ f x) :
    ∀ n x, x ∈ actualRounds seed lower constant threshold n → (x : ℝ) < barrier := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro candidate hc
    obtain ⟨anchor, ha, hcert⟩ := hc
    by_contra hn
    exact actual_design_domain_valid_cone_cannot_cross_an_unsafe_design_point
      design f constant hf threshold (lower (n+1) anchor) anchor barrier candidate
      (hconfidence (n+1) anchor) hunsafe (ih anchor ha) (le_of_not_gt hn) hcert

theorem actual_design_domain_admissible_queries_and_reports_cannot_cross_the_hole
    (design : Set ℝ) (f : design → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold : ℝ) (barrier : design)
    (hunsafe : f barrier < threshold) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x : ℝ) < barrier) (lower : ℕ → design → ℝ)
    (hconfidence : ∀ n x, lower n x ≤ f x) (query report : ℕ → design)
    (hquery : ∀ n, query n ∈ actualRounds seed lower constant threshold n)
    (hreport : ∀ n, report n ∈ actualRounds seed lower constant threshold n) :
    (∀ n, (query n : ℝ) < barrier) ∧ (∀ n, (report n : ℝ) < barrier) := by
  have hall := actual_design_domain_confidence_rounds_never_cross_the_unsafe_hole
    design f constant hf threshold barrier hunsafe seed hseed lower hconfidence
  exact ⟨fun n => hall n (query n) (hquery n), fun n => hall n (report n) (hreport n)⟩

theorem actual_design_domain_nonnegative_slack_reachable_benchmark_cannot_cross_the_hole
    (design : Set ℝ) (f : design → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold epsilon : ℝ) (barrier : design)
    (hunsafe : f barrier < threshold) (hepsilon : 0 ≤ epsilon) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x : ℝ) < barrier) :
    ∀ x ∈ actualReachableClosure f constant threshold epsilon seed, (x : ℝ) < barrier := by
  have hall : ∀ n x, x ∈ actualReachIterates f constant threshold epsilon seed n →
      (x : ℝ) < barrier := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      intro candidate hc
      rcases hc with hc | ⟨anchor, ha, hcert⟩
      · exact ih candidate hc
      · by_contra hn
        exact actual_design_domain_valid_cone_cannot_cross_an_unsafe_design_point
          design f constant hf threshold (f anchor - epsilon) anchor barrier candidate
          (by linarith) hunsafe (ih anchor ha) (le_of_not_gt hn) hcert
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact hall n x hn

end SafeLearning.CompleteModulesSafeOptDisconnectedConsequences
