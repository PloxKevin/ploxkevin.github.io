import SafeLearning.CompleteModulesSafeOptReachableClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptDisconnectedGeometry
open CompleteModulesSafeOptPracticeTheorems CompleteModulesSafeOptReachableClosure

theorem actual_one_dimensional_valid_cone_cannot_certify_across_an_unsafe_intermediate_point
    (f : ℝ → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (threshold lower anchor barrier candidate : ℝ)
    (hlower : lower≤f anchor) (hunsafe : f barrier<threshold)
    (hleft : anchor<barrier) (hright : barrier≤candidate) :
    ¬threshold≤lower-constant*dist anchor candidate := by
  have hd : dist anchor barrier≤dist anchor candidate := by
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  have ht := actual_metric_lipschitz_lower_confidence_transfer f constant hf anchor barrier lower hlower
  have hc := mul_le_mul_of_nonneg_left hd constant.coe_nonneg
  intro hcert
  linarith

theorem actual_regular_grid_source_confidence_rounds_all_stay_on_the_seed_side_of_an_unsafe_hole
    (design : Set ℝ) (f : ℝ → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold barrier : ℝ)
    (hunsafe : f barrier<threshold) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x:ℝ)<barrier) (lower : ℕ → design → ℝ)
    (hconfidence : ∀ n x, lower n x≤f x) :
    ∀ n x, x ∈ actualRounds seed lower constant threshold n → (x:ℝ)<barrier := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro candidate hc
    obtain ⟨anchor,ha,hcert⟩ := hc
    have hleft := ih anchor ha
    by_contra hn
    have hright : barrier≤(candidate:ℝ) := le_of_not_gt hn
    have himpossible := actual_one_dimensional_valid_cone_cannot_certify_across_an_unsafe_intermediate_point
      f constant hf threshold (lower (n+1) anchor) anchor barrier candidate
      (hconfidence (n+1) anchor) hunsafe hleft hright
    exact himpossible (by simpa only [Subtype.dist_eq] using hcert)

theorem actual_every_admissible_report_and_query_stays_on_the_seed_side
    (design : Set ℝ) (f : ℝ → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold barrier : ℝ)
    (hunsafe : f barrier<threshold) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x:ℝ)<barrier) (lower : ℕ → design → ℝ)
    (hconfidence : ∀ n x, lower n x≤f x)
    (query report : ℕ → design)
    (hquery : ∀ n, query n ∈ actualRounds seed lower constant threshold n)
    (hreport : ∀ n, report n ∈ actualRounds seed lower constant threshold n) :
    (∀ n, (query n:ℝ)<barrier) ∧ (∀ n, (report n:ℝ)<barrier) := by
  have hall := actual_regular_grid_source_confidence_rounds_all_stay_on_the_seed_side_of_an_unsafe_hole
    design f constant hf threshold barrier hunsafe seed hseed lower hconfidence
  exact ⟨fun n => hall n (query n) (hquery n),fun n => hall n (report n) (hreport n)⟩

theorem actual_nonnegative_slack_reachable_benchmark_also_stays_on_the_seed_side
    (design : Set ℝ) (f : ℝ → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold barrier epsilon : ℝ)
    (hunsafe : f barrier<threshold) (hepsilon : 0≤epsilon) (seed : Set design)
    (hseed : ∀ x ∈ seed, (x:ℝ)<barrier) :
    ∀ x ∈ actualReachableClosure (fun x : design => f x) constant threshold epsilon seed,
      (x:ℝ)<barrier := by
  have hall : ∀ n x, x ∈ actualReachIterates (fun x : design => f x) constant threshold epsilon seed n →
      (x:ℝ)<barrier := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      intro candidate hc
      rcases hc with hc | ⟨anchor,ha,hcert⟩
      · exact ih candidate hc
      · have hleft := ih anchor ha
        by_contra hn
        have himpossible := actual_one_dimensional_valid_cone_cannot_certify_across_an_unsafe_intermediate_point
          f constant hf threshold (f anchor-epsilon) anchor barrier candidate
          (by linarith) hunsafe hleft (le_of_not_gt hn)
        exact himpossible (by simpa only [Subtype.dist_eq] using hcert)
  intro x hx
  obtain ⟨n,hn⟩ := mem_iUnion.mp hx
  exact hall n x hn

theorem actual_euclidean_certificate_ball_contains_every_point_of_the_segment_to_a_certified_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (anchor candidate : E) (radius : ℝ) (hradius : 0≤radius)
    (hcertified : candidate ∈ Metric.closedBall anchor radius) :
    segment ℝ anchor candidate ⊆ Metric.closedBall anchor radius := by
  exact (convex_closedBall anchor radius).segment_subset
    (by simpa only [Metric.mem_closedBall,dist_self] using hradius) hcertified

end SafeLearning.CompleteModulesSafeOptDisconnectedGeometry
