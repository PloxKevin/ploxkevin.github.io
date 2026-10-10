import SafeLearning.CompleteModulesSafeOptInitializedRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSafeOptMeasurable
open MeasureTheory Set
open scoped NNReal
open CompleteModulesSafeOptInitializedRun CompleteModulesSafeOptConfidenceIntersections
open CompleteModulesSafeOptPracticeTheorems

variable {X Ω : Type*} [MeasurableSpace Ω]

/-- Actual seed initialization and every finite lower-band intersection
preserve measurability of the computed lower endpoint. -/
theorem actual_seed_initialized_contained_lower_is_measurable
    (seed : Set X) (threshold : ℝ) (rawLower : Ω → ℕ → X → ℝ)
    (hraw : ∀ n x, Measurable (fun omega => rawLower omega n x)) :
    ∀ n x, Measurable (fun omega => actualContainedLower seed threshold (rawLower omega) n x) := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    by_cases hx : x ∈ seed
    · simpa only [actualContainedLower, actualLower, actualInitializedLower, ite_eq_left hx] using
        measurable_const.max (hraw 1 x)
    · simpa only [actualContainedLower, actualLower, actualInitializedLower, ite_eq_right hx] using hraw 1 x
  | succ n ih =>
    intro x
    simpa only [actualContainedLower, actualLower] using (ih x).max (hraw (n + 2) x)

variable [PseudoMetricSpace X] [Fintype X]

/-- Membership in every genuinely computed source safe round is measurable:
the finite expansion takes the actual union of measurable anchor certificates. -/
theorem actual_finite_source_safe_round_membership_is_measurable
    (seed : Set X) (lower : Ω → ℕ → X → ℝ) (constant : ℝ≥0) (threshold : ℝ)
    (hlower : ∀ n x, Measurable (fun omega => lower omega n x)) :
    ∀ n x, MeasurableSet {omega | x ∈ actualRounds seed (lower omega) constant threshold n} := by
  intro n
  induction n with
  | zero =>
    intro x
    by_cases hx : x ∈ seed <;> simp [actualRounds, hx]
  | succ n ih =>
    intro x
    have heq : {omega | x ∈ actualRounds seed (lower omega) constant threshold (n + 1)} =
        ⋃ anchor : X, {omega | anchor ∈ actualRounds seed (lower omega) constant threshold n} ∩
          {omega | threshold ≤ lower omega (n + 1) anchor - constant * dist anchor x} := by
      ext omega
      simp only [actualRounds, actualExpansion, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    rw [heq]
    exact MeasurableSet.iUnion (fun anchor => (ih anchor).inter
      (measurableSet_le measurable_const ((hlower (n + 1) anchor).sub_const _)))

/-- The exact initialized finite safe set inherits membership measurability
from its actual seed floor, finite intersections and source expansion recursion. -/
theorem actual_initialized_safe_finset_membership_is_measurable
    (seed : Set X) (threshold : ℝ) (rawLower : Ω → ℕ → X → ℝ) (constant : ℝ≥0)
    (hraw : ∀ n x, Measurable (fun omega => rawLower omega n x)) :
    ∀ n x, MeasurableSet {omega | x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n} := by
  have hcontained := actual_seed_initialized_contained_lower_is_measurable seed threshold rawLower hraw
  have hs := actual_finite_source_safe_round_membership_is_measurable seed
    (fun omega => actualInitializedSourceLower seed threshold (rawLower omega)) constant threshold
    (fun n x => hcontained (n - 1) x)
  intro n x
  simpa only [actualInitializedSafeFinset, Set.Finite.mem_toFinset] using hs (n + 1) x

/-- The joint event of every actual query and every point of every computed
finite safe set satisfying the threshold is a genuine measurable event. -/
theorem actual_initialized_query_and_every_safe_round_safety_event_is_measurable
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (f : X → ℝ) (seed : Set X) (threshold : ℝ) (constant : ℝ≥0)
    (rawLower : Ω → ℕ → X → ℝ)
    (hraw : ∀ n x, Measurable (fun omega => rawLower omega n x))
    (query : ℕ → Ω → X) (hq : ∀ n, Measurable (query n)) :
    MeasurableSet {omega | (∀ n, threshold ≤ f (query n omega)) ∧
      ∀ n x, x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n → threshold ≤ f x} := by
  have hmembership := actual_initialized_safe_finset_membership_is_measurable seed threshold rawLower constant hraw
  have hqueries : MeasurableSet {omega | ∀ n, threshold ≤ f (query n omega)} := by
    have heq : {omega | ∀ n, threshold ≤ f (query n omega)} =
        ⋂ n, {omega | threshold ≤ f (query n omega)} := by ext omega; simp
    rw [heq]
    exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const
      ((measurable_of_countable f).comp (hq n)))
  have hrounds : MeasurableSet {omega | ∀ n x,
      x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n → threshold ≤ f x} := by
    have heq : {omega | ∀ n x,
        x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n → threshold ≤ f x} =
        ⋂ n, ⋂ x, {omega |
          x ∈ actualInitializedSafeFinset seed threshold (rawLower omega) constant n → threshold ≤ f x} := by
      ext omega
      simp
    rw [heq]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro x
    by_cases hx : threshold ≤ f x
    · simpa only [hx, implies_true, setOf_true] using (MeasurableSet.univ : MeasurableSet (univ : Set Ω))
    · simpa only [hx, imp_false, Set.compl_setOf] using (hmembership n x).compl
  exact hqueries.inter hrounds

end SafeLearning.CompleteModulesLandscapeSafeOptMeasurable

#print axioms SafeLearning.CompleteModulesLandscapeSafeOptMeasurable.actual_seed_initialized_contained_lower_is_measurable
#print axioms SafeLearning.CompleteModulesLandscapeSafeOptMeasurable.actual_finite_source_safe_round_membership_is_measurable
#print axioms SafeLearning.CompleteModulesLandscapeSafeOptMeasurable.actual_initialized_safe_finset_membership_is_measurable
#print axioms SafeLearning.CompleteModulesLandscapeSafeOptMeasurable.actual_initialized_query_and_every_safe_round_safety_event_is_measurable
