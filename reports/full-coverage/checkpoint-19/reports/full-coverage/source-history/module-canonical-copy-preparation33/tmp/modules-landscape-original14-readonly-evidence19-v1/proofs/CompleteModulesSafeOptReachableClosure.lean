import SafeLearning.CompleteModulesSafeOptPracticeTheorems

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptReachableClosure
open SafeLearning.CompleteModulesSafeOptPracticeTheorems

def actualReach {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (constant : NNReal) (threshold epsilon : ℝ) (old : Set X) : Set X :=
  old ∪ actualExpansion old (fun x => f x-epsilon) constant threshold

def actualReachIterates {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (constant : NNReal) (threshold epsilon : ℝ) (seed : Set X) : ℕ → Set X
  | 0 => seed
  | n+1 => actualReach f constant threshold epsilon (actualReachIterates f constant threshold epsilon seed n)

def actualReachableClosure {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (constant : NNReal) (threshold epsilon : ℝ) (seed : Set X) : Set X :=
  ⋃ n, actualReachIterates f constant threshold epsilon seed n

theorem actual_reach_operator_keeps_every_old_point_and_is_monotone
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (constant : NNReal) (threshold epsilon : ℝ) :
    (∀ old : Set X, old ⊆ actualReach f constant threshold epsilon old) ∧
      Monotone (actualReach f constant threshold epsilon) := by
  constructor
  · exact fun _ _ h => Or.inl h
  · intro a b hab x hx
    rcases hx with hx | ⟨anchor,ha,hcert⟩
    · exact Or.inl (hab hx)
    · exact Or.inr ⟨anchor,hab ha,hcert⟩

theorem actual_source_iterated_reachable_closure_is_a_genuine_fixed_point
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (constant : NNReal) (threshold epsilon : ℝ) (seed : Set X) :
    actualReach f constant threshold epsilon (actualReachableClosure f constant threshold epsilon seed)=
      actualReachableClosure f constant threshold epsilon seed := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | ⟨anchor,ha,hcert⟩
    · exact hx
    · obtain ⟨n,hn⟩ := mem_iUnion.mp ha
      apply mem_iUnion.mpr
      refine ⟨n+1,?_⟩
      exact Or.inr ⟨anchor,hn,hcert⟩
  · exact fun hx => Or.inl hx

theorem actual_source_safeopt_certificates_never_leave_the_actual_zero_slack_reachable_closure
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (constant : NNReal) (threshold : ℝ) (seed : Set X)
    (lower : ℕ → X → ℝ) (hconfidence : ∀ n x, lower n x ≤ f x) :
    ∀ n, actualRounds seed lower constant threshold n ⊆ actualReachableClosure f constant threshold 0 seed := by
  intro n
  induction n with
  | zero =>
    intro x hx
    exact mem_iUnion.mpr ⟨0,hx⟩
  | succ n ih =>
    intro x hx
    obtain ⟨anchor,ha,hcert⟩ := hx
    have hc : threshold ≤ (f anchor-0)-constant*dist anchor x := by
      have hl := hconfidence (n+1) anchor
      linarith
    have hr : x ∈ actualReach f constant threshold 0 (actualReachableClosure f constant threshold 0 seed) :=
      Or.inr ⟨anchor,ih ha,hc⟩
    rwa [actual_source_iterated_reachable_closure_is_a_genuine_fixed_point] at hr

theorem actual_nonnegative_slack_reachable_closure_is_safe_under_the_true_lipschitz_bound
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold epsilon : ℝ) (heps : 0 ≤ epsilon)
    (seed : Set X) (hseed : ∀ x ∈ seed, threshold ≤ f x) :
    ∀ x ∈ actualReachableClosure f constant threshold epsilon seed, threshold ≤ f x := by
  have hi : ∀ n x, x ∈ actualReachIterates f constant threshold epsilon seed n → threshold ≤ f x := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      intro x hx
      rcases hx with hx | ⟨anchor,_ha,hcert⟩
      · exact ih x hx
      · have htransfer := actual_metric_lipschitz_lower_confidence_transfer f constant hf anchor x
          (f anchor-epsilon) (by linarith)
        exact hcert.trans htransfer
  intro x hx
  obtain ⟨n,hn⟩ := mem_iUnion.mp hx
  exact hi n x hn

theorem actual_seed_confidence_floor_certifies_itself_and_includes_the_seed_in_round_one
    {X : Type*} [PseudoMetricSpace X] (constant : NNReal) (threshold : ℝ)
    (seed : Set X) (lower : ℕ → X → ℝ) (hfloor : ∀ x ∈ seed, threshold ≤ lower 1 x) :
    seed ⊆ actualRounds seed lower constant threshold 1 := by
  intro x hx
  refine ⟨x,hx,?_⟩
  simpa using hfloor x hx

theorem actual_unsafe_seed_is_incompatible_with_a_valid_seed_lower_confidence_floor
    (value lower threshold : ℝ) (hunsafe : value<threshold) (hfloor : threshold≤lower) :
    ¬lower≤value := by linarith

end SafeLearning.CompleteModulesSafeOptReachableClosure
