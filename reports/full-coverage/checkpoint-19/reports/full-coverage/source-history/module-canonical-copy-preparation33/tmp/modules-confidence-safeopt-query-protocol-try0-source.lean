import SafeLearning.CompleteModulesSafeOptInitializedRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol
open Set
open CompleteModulesSafeOptFiniteOptimality CompleteModulesSafeOptInitializedRun

variable {X : Type*}

/-- The actual finite width maximizer belongs to its computed safe set:
its literal candidate union is a filter of precisely that finite set. -/
theorem actual_finite_width_maximizer_is_a_member_of_its_computed_safe_finset
    (safe : Finset X) (lower upper : X → ℝ) (cost : X → X → ℝ) (threshold : ℝ)
    (hsafeNonempty : safe.Nonempty) (horderedBands : ∀ x ∈ safe, lower x ≤ upper x) :
    actualFiniteQuery safe lower upper cost threshold hsafeNonempty horderedBands ∈ safe := by
  have hcandidate :=
    (actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
      safe lower upper cost threshold hsafeNonempty horderedBands).1
  unfold actualFiniteCandidates at hcandidate
  exact (Finset.mem_filter.mp hcandidate).1

variable [PseudoMetricSpace X] [Fintype X]

/-- At source round n+1 the actual width maximizer uses the initialized
computed safe set and its actual contained endpoints at query index n. -/
theorem actual_initialized_contained_band_width_maximizer_is_in_the_computed_safe_finset
    (seed : Set X) (threshold : ℝ) (rawLower rawUpper : ℕ → X → ℝ)
    (constant : ℝ≥0) (n : ℕ)
    (hsafeNonempty : (actualInitializedSafeFinset seed threshold rawLower constant n).Nonempty)
    (horderedBands : ∀ x ∈ actualInitializedSafeFinset seed threshold rawLower constant n,
      actualContainedLower seed threshold rawLower n x ≤ actualContainedUpper rawUpper n x) :
    actualFiniteQuery (actualInitializedSafeFinset seed threshold rawLower constant n)
      (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
      (fun x y => (constant : ℝ) * dist x y) threshold hsafeNonempty horderedBands ∈
        actualInitializedSafeFinset seed threshold rawLower constant n := by
  exact actual_finite_width_maximizer_is_a_member_of_its_computed_safe_finset
    (actualInitializedSafeFinset seed threshold rawLower constant n)
    (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
    (fun x y => (constant : ℝ) * dist x y) threshold hsafeNonempty horderedBands

/-- A stream satisfying the literal initialized width-maximizing query
protocol supplies computed-set membership at every outcome and round.
Nonempty sets and ordered contained bands express protocol well-definedness. -/
theorem actual_initialized_width_maximizing_query_protocol_supplies_every_computed_set_membership
    {Ω : Type*} (seed : Set X) (threshold : ℝ)
    (rawLower rawUpper : Ω → ℕ → X → ℝ) (constant : ℝ≥0) (query : ℕ → Ω → X)
    (hsafeNonempty : ∀ omega n,
      (actualInitializedSafeFinset seed threshold (rawLower omega) constant n).Nonempty)
    (horderedBands : ∀ omega n x,
      x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n →
        actualContainedLower seed threshold (rawLower omega) n x ≤
          actualContainedUpper (rawUpper omega) n x)
    (hprotocol : ∀ omega n, query n omega =
      actualFiniteQuery (actualInitializedSafeFinset seed threshold (rawLower omega) constant n)
        (actualContainedLower seed threshold (rawLower omega) n)
        (actualContainedUpper (rawUpper omega) n)
        (fun x y => (constant : ℝ) * dist x y) threshold
        (hsafeNonempty omega n) (horderedBands omega n)) :
    ∀ omega n, query n omega ∈
      actualInitializedSafeFinset seed threshold (rawLower omega) constant n := by
  intro omega n
  rw [hprotocol omega n]
  exact actual_initialized_contained_band_width_maximizer_is_in_the_computed_safe_finset
    seed threshold (rawLower omega) (rawUpper omega) constant n
    (hsafeNonempty omega n) (horderedBands omega n)

end SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol
