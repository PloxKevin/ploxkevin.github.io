import SafeLearning.CompleteModulesSafeOptConfidenceInitialization
import SafeLearning.CompleteModulesSafeOptFiniteOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteModulesSafeOptInitializedRun

open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure
open SafeLearning.CompleteModulesSafeOptConfidenceIntersections
open SafeLearning.CompleteModulesSafeOptConfidenceInitialization
open SafeLearning.CompleteModulesSafeOptFiniteOptimality

variable {X : Type*}

/-- The first source interval intersects the seed halfline with raw band 1. -/
def actualInitializedLower (seed : Set X) (threshold : ℝ) (rawLower : ℕ → X → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ seed then max threshold (rawLower 1 x) else rawLower 1 x

/-- Query index n corresponds to the source interval C_(n+1). -/
def actualContainedLower (seed : Set X) (threshold : ℝ) (rawLower : ℕ → X → ℝ)
    (n : ℕ) (x : X) : ℝ :=
  actualLower (actualInitializedLower seed threshold rawLower x) (fun j => rawLower (j + 2) x) n

def actualContainedUpper (rawUpper : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  actualUpper (rawUpper 1 x) (fun j => rawUpper (j + 2) x) n

/-- The constructed finite endpoints are exactly the positive-round source
confidence intersections, including the genuine halfline seed initialization. -/
theorem actual_initialized_finite_endpoints_equal_the_literal_source_confidence_intersections
    (seed : Set X) (threshold : ℝ) (rawLower rawUpper : ℕ → X → ℝ) :
    ∀ n x, actualConfidence seed threshold (fun j x => Icc (rawLower j x) (rawUpper j x)) (n + 1) x =
      Icc (actualContainedLower seed threshold rawLower n x) (actualContainedUpper rawUpper n x) := by
  classical
  intro n x
  have hfirst : actualConfidence seed threshold (fun j x => Icc (rawLower j x) (rawUpper j x)) 1 x =
      Icc (actualInitializedLower seed threshold rawLower x) (rawUpper 1 x) := by
    by_cases hx : x ∈ seed
    · simpa only [actualInitializedLower,if_pos hx] using
        (actual_source_seed_initial_confidence_interval_has_the_derived_maximum_lower_endpoint
          seed threshold (fun j x => Icc (rawLower j x) (rawUpper j x)) x hx
          (rawLower 1 x) (rawUpper 1 x) rfl).1
    · ext value
      simp [actualConfidence,actualInitializedLower,hx,Nat.lt_one_iff]
  have hinterval : ∀ j, actualConfidence seed threshold
      (fun i x => Icc (rawLower i x) (rawUpper i x)) (j + 1) x =
      actualInterval (actualInitializedLower seed threshold rawLower x) (rawUpper 1 x)
        (fun i => rawLower (i + 2) x) (fun i => rawUpper (i + 2) x) j := by
    intro j
    induction j with
    | zero => exact hfirst
    | succ j ih =>
      rw [actual_next_confidence_set_is_exactly_the_previous_set_intersected_with_the_new_band,
        ih,actualInterval]
  rw [hinterval n,actual_finite_confidence_intersection_has_the_literal_max_lower_min_upper_endpoints]
  rfl

/-- Each constructed contained interval is inside its actual current raw band. -/
theorem actual_initialized_interval_is_contained_in_its_current_source_raw_band
    (seed : Set X) (threshold : ℝ) (rawLower rawUpper : ℕ → X → ℝ) :
    ∀ n x, Icc (actualContainedLower seed threshold rawLower n x) (actualContainedUpper rawUpper n x) ⊆
      Icc (rawLower (n + 1) x) (rawUpper (n + 1) x) := by
  classical
  intro n x value hv
  have hsource : value ∈ actualConfidence seed threshold
      (fun j x => Icc (rawLower j x) (rawUpper j x)) (n + 1) x := by
    rw [actual_initialized_finite_endpoints_equal_the_literal_source_confidence_intersections]
    exact hv
  exact hsource.2 n (Nat.lt_succ_self n)

/-- Actual raw-band truth and safe seeds derive valid constructed bands,
monotone lower/upper endpoints, and the first-round seed floor. -/
theorem actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
    (f : X → ℝ) (seed : Set X) (threshold : ℝ) (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x))
    (hseed : ∀ x ∈ seed, threshold ≤ f x) :
    (∀ n x, actualContainedLower seed threshold rawLower n x ≤ f x ∧
      f x ≤ actualContainedUpper rawUpper n x) ∧
    (∀ i j, i ≤ j → ∀ x, actualContainedLower seed threshold rawLower i x ≤
      actualContainedLower seed threshold rawLower j x) ∧
    (∀ i j, i ≤ j → ∀ x, actualContainedUpper rawUpper j x ≤ actualContainedUpper rawUpper i x) ∧
    ∀ x ∈ seed, threshold ≤ actualContainedLower seed threshold rawLower 0 x := by
  classical
  have htruth := actual_one_joint_confidence_event_and_seed_safety_preserve_every_intersection
    f seed threshold (fun j x => Icc (rawLower j x) (rawUpper j x)) hraw hseed
  refine ⟨?_,?_,?_,?_⟩
  · intro n x
    have h := htruth (n + 1) x
    rw [actual_initialized_finite_endpoints_equal_the_literal_source_confidence_intersections] at h
    exact h
  · intro i j hij x
    exact (monotone_nat_of_le_succ (fun n =>
      (actual_intersected_lower_increases_upper_decreases_and_width_decreases
        (actualInitializedLower seed threshold rawLower x) (rawUpper 1 x)
        (fun k => rawLower (k + 2) x) (fun k => rawUpper (k + 2) x) n).1)) hij
  · intro i j hij x
    exact (antitone_nat_of_succ_le (fun n =>
      (actual_intersected_lower_increases_upper_decreases_and_width_decreases
        (actualInitializedLower seed threshold rawLower x) (rawUpper 1 x)
        (fun k => rawLower (k + 2) x) (fun k => rawUpper (k + 2) x) n).2.1)) hij
  · intro x hx
    simpa only [actualContainedLower,actualLower,actualInitializedLower,if_pos hx] using
      le_max_left threshold (rawLower 1 x)

variable [PseudoMetricSpace X]

/-- Persisting actual certificates derive nested source rounds. This proof
does not require a new point's own lower band to clear the threshold. -/
theorem actual_seed_floor_and_increasing_lower_bands_make_the_source_safe_rounds_monotone
    (seed : Set X) (lower : ℕ → X → ℝ) (constant : NNReal) (threshold : ℝ)
    (hfloor : ∀ x ∈ seed, threshold ≤ lower 1 x)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x) :
    Monotone (actualRounds seed lower constant threshold) := by
  have hstep : ∀ n, actualRounds seed lower constant threshold n ⊆
      actualRounds seed lower constant threshold (n + 1) := by
    intro n
    induction n with
    | zero => exact actual_seed_confidence_floor_certifies_itself_and_includes_the_seed_in_round_one
        constant threshold seed lower hfloor
    | succ n ih =>
      intro candidate hc
      obtain ⟨anchor,ha,hcertificate⟩ := hc
      refine ⟨anchor,ih ha,?_⟩
      have h := hlower (n + 1) (n + 2) (Nat.le_succ _) anchor
      linarith
  exact monotone_nat_of_le_succ hstep

/-- The source lower endpoint at round 0 is unused by the recursive safe
update. Positive round n+1 has the constructed endpoint at query index n. -/
def actualInitializedSourceLower (seed : Set X) (threshold : ℝ) (rawLower : ℕ → X → ℝ)
    (round : ℕ) : X → ℝ := actualContainedLower seed threshold rawLower (round - 1)

variable [Fintype X]

def actualInitializedSafeFinset (seed : Set X) (threshold : ℝ) (rawLower : ℕ → X → ℝ)
    (constant : NNReal) (n : ℕ) : Finset X :=
  (actualRounds seed (actualInitializedSourceLower seed threshold rawLower) constant threshold (n + 1)).toFinite.toFinset

def actualZeroReachableFinset (f : X → ℝ) (constant : NNReal) (threshold : ℝ) (seed : Set X) : Finset X :=
  (actualReachableClosure f constant threshold 0 seed).toFinite.toFinset

/-- The constructed finite run uses the literal source expansion update. -/
theorem actual_initialized_finite_run_has_the_literal_source_safe_update
    (seed : Set X) (threshold : ℝ) (rawLower : ℕ → X → ℝ) (constant : NNReal) :
    ∀ n, (actualInitializedSafeFinset seed threshold rawLower constant (n + 1) : Set X) =
      actualExpansion (actualInitializedSafeFinset seed threshold rawLower constant n : Set X)
        (actualContainedLower seed threshold rawLower (n + 1)) constant threshold := by
  intro n
  simp only [actualInitializedSafeFinset,Set.Finite.coe_toFinset]
  rfl

/-- The finite bound is exactly the actual zero-reachable set, and its
cardinality is the source's actual finite zero-reachable cardinality. -/
theorem actual_zero_reachable_finset_has_exact_membership_and_cardinality
    (f : X → ℝ) (constant : NNReal) (threshold : ℝ) (seed : Set X) :
    (actualZeroReachableFinset f constant threshold seed : Set X) =
      actualReachableClosure f constant threshold 0 seed ∧
    (actualZeroReachableFinset f constant threshold seed).card =
      (actualReachableClosure f constant threshold 0 seed).ncard := by
  have hset : (actualZeroReachableFinset f constant threshold seed : Set X) =
      actualReachableClosure f constant threshold 0 seed := Set.Finite.coe_toFinset _
  refine ⟨hset,?_⟩
  rw [← hset,Set.ncard_coe_finset]

/-- The literal initialized intersections and source safe updates construct
an actual nested nonempty finite run contained in its zero-reachable bound.
True seed safety and Lipschitz transfer prove every point of this run safe. -/
theorem actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
    (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f) (threshold : ℝ)
    (seed : Set X) (hseed_nonempty : seed.Nonempty) (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x)) :
    (∀ n, (actualInitializedSafeFinset seed threshold rawLower constant n).Nonempty) ∧
    (∀ i j, i ≤ j → actualInitializedSafeFinset seed threshold rawLower constant i ⊆
      actualInitializedSafeFinset seed threshold rawLower constant j) ∧
    (∀ n, actualInitializedSafeFinset seed threshold rawLower constant n ⊆
      actualZeroReachableFinset f constant threshold seed) ∧
    seed ⊆ (actualInitializedSafeFinset seed threshold rawLower constant 0 : Set X) ∧
    ∀ n x, x ∈ actualInitializedSafeFinset seed threshold rawLower constant n → threshold ≤ f x := by
  classical
  have hbands := actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
    f seed threshold rawLower rawUpper hraw hseed
  have hfloor : ∀ x ∈ seed, threshold ≤ actualInitializedSourceLower seed threshold rawLower 1 x := by
    simpa only [actualInitializedSourceLower,Nat.sub_self] using hbands.2.2.2
  have hsource_mono := actual_seed_floor_and_increasing_lower_bands_make_the_source_safe_rounds_monotone
    seed (actualInitializedSourceLower seed threshold rawLower) constant threshold hfloor
    (fun i j hij x => hbands.2.1 (i - 1) (j - 1) (Nat.sub_le_sub_right hij 1) x)
  have hsource_valid : ∀ n x, actualInitializedSourceLower seed threshold rawLower n x ≤ f x :=
    fun n x => (hbands.1 (n - 1) x).1
  have hcontains := actual_source_safeopt_certificates_never_leave_the_actual_zero_slack_reachable_closure
    f constant threshold seed (actualInitializedSourceLower seed threshold rawLower) hsource_valid
  have hsafe := (actual_joint_confidence_and_safe_seed_prove_every_expanded_round_and_every_selected_query_safe
    f constant hf threshold seed (actualInitializedSourceLower seed threshold rawLower) hsource_valid hseed).1
  have hseed_round := actual_seed_confidence_floor_certifies_itself_and_includes_the_seed_in_round_one
    constant threshold seed (actualInitializedSourceLower seed threshold rawLower) hfloor
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨x,hx⟩ := hseed_nonempty
    refine ⟨x,?_⟩
    simp only [actualInitializedSafeFinset,Set.Finite.mem_toFinset]
    exact hsource_mono (Nat.le_add_left 1 n) (hseed_round hx)
  · intro i j hij x hx
    simp only [actualInitializedSafeFinset,Set.Finite.mem_toFinset] at hx ⊢
    exact hsource_mono (Nat.add_le_add_right hij 1) hx
  · intro n x hx
    simp only [actualInitializedSafeFinset,actualZeroReachableFinset,Set.Finite.mem_toFinset] at hx ⊢
    exact hcontains (n + 1) hx
  · intro x hx
    simp only [actualInitializedSafeFinset,Set.Finite.mem_toFinset]
    exact hseed_round hx
  · intro n x hx
    simp only [actualInitializedSafeFinset,Set.Finite.mem_toFinset] at hx
    exact hsafe (n + 1) x hx

end SafeLearning.CompleteModulesSafeOptInitializedRun
