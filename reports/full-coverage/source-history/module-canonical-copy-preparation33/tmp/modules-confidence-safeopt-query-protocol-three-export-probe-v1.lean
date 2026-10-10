import SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol
open Set
open scoped NNReal
open CompleteModulesSafeOptFiniteOptimality CompleteModulesSafeOptInitializedRun

variable {X : Type*}



example
    (safe : Finset X) (lower upper : X → ℝ) (cost : X → X → ℝ) (threshold : ℝ)
    (hsafeNonempty : safe.Nonempty) (horderedBands : ∀ x ∈ safe, lower x ≤ upper x) :
    actualFiniteQuery safe lower upper cost threshold hsafeNonempty horderedBands ∈ safe := by
  apply SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_finite_width_maximizer_is_a_member_of_its_computed_safe_finset <;> assumption


variable [PseudoMetricSpace X] [Fintype X]

example
    (seed : Set X) (threshold : ℝ) (rawLower rawUpper : ℕ → X → ℝ)
    (constant : ℝ≥0) (n : ℕ)
    (hsafeNonempty : (actualInitializedSafeFinset seed threshold rawLower constant n).Nonempty)
    (horderedBands : ∀ x ∈ actualInitializedSafeFinset seed threshold rawLower constant n,
      actualContainedLower seed threshold rawLower n x ≤ actualContainedUpper rawUpper n x) :
    actualFiniteQuery (actualInitializedSafeFinset seed threshold rawLower constant n)
      (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
      (fun x y => (constant : ℝ) * dist x y) threshold hsafeNonempty horderedBands ∈
        actualInitializedSafeFinset seed threshold rawLower constant n := by
  apply SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_initialized_contained_band_width_maximizer_is_in_the_computed_safe_finset <;> assumption


example
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
  apply SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_initialized_width_maximizing_query_protocol_supplies_every_computed_set_membership <;> assumption


end SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol

#print axioms SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_finite_width_maximizer_is_a_member_of_its_computed_safe_finset

#print axioms SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_initialized_contained_band_width_maximizer_is_in_the_computed_safe_finset

#print axioms SafeLearning.CompleteModulesLandscapeSafeOptQueryProtocol.actual_initialized_width_maximizing_query_protocol_supplies_every_computed_set_membership
