import SafeLearning.CompleteModulesSafeOptInitializedRun
import SafeLearning.CompleteModulesSafeOptKernelRunOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteModulesSafeOptReachableKernelRun

open SafeLearning.CompleteModulesSafeOptInitializedRun
open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptKernelRunOptimality
open SafeLearning.CompleteModulesSafeOptGPInformationBudget
open SafeLearning.CompleteModulesSafeOptReachableClosure

variable {X : Type*} [PseudoMetricSpace X] [Fintype X]

/-- The source's actual width-maximizing query in S_(n+1), using the literal
constructed C_(n+1) endpoints and the derived nonempty safe run. -/
def actualInitializedQuery (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (threshold : ℝ) (seed : Set X) (hseed_nonempty : seed.Nonempty)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x)) (n : ℕ) : X :=
  actualFiniteQuery (actualInitializedSafeFinset seed threshold rawLower constant n)
    (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
    (fun x y => constant * dist x y) threshold
    ((actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
      f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw).1 n)
    (fun x _ =>
      ((actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
        f seed threshold rawLower rawUpper hraw hseed).1 n x).1.trans
      ((actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
        f seed threshold rawLower rawUpper hraw hseed).1 n x).2)

/-- The actual source recommendation maximizes the constructed lower band. -/
def actualInitializedReport (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (threshold : ℝ) (seed : Set X) (hseed_nonempty : seed.Nonempty)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x)) (n : ℕ) : X :=
  actualFiniteReport (actualInitializedSafeFinset seed threshold rawLower constant n)
    (actualContainedLower seed threshold rawLower n)
    ((actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
      f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw).1 n)

/-- Every genuine width-maximizing source query is safe at its true value,
from seed safety, valid raw confidence, and actual Lipschitz certificates. -/
theorem actual_initialized_width_maximizing_source_query_is_safe
    (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (threshold : ℝ) (seed : Set X) (hseed_nonempty : seed.Nonempty)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x)) :
    ∀ n, threshold ≤ f (actualInitializedQuery f constant hf threshold seed hseed_nonempty
      hseed rawLower rawUpper hraw n) := by
  classical
  intro n
  have hrun := actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
    f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw
  have hbands := actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
    f seed threshold rawLower rawUpper hraw hseed
  have hquery := (actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    (actualInitializedSafeFinset seed threshold rawLower constant n)
    (actualContainedLower seed threshold rawLower n) (actualContainedUpper rawUpper n)
    (fun x y => constant * dist x y) threshold (hrun.1 n)
    (fun x _ => (hbands.1 n x).1.trans (hbands.1 n x).2)).1
  exact hrun.2.2.2.2 n _ (Finset.mem_filter.mp hquery).1

variable [DecidableEq X] [Nonempty X]

/-- The initialized source run is safe and becomes epsilon optimal against
its actual reachable benchmark under the exact zero-reachable cardinality
window budget. Safe-set nesting, nonemptiness, seed retention, valid contained
endpoints, actual updates and the finite bound are all derived internally.
The raw-confidence event and actual GP raw-band shape remain explicit. Query
index n represents source round n+1, so the horizon certifies source reports
at horizon+1 and later; no literal unrounded t-star theorem is asserted. -/
theorem actual_initialized_safeopt_kernel_run_is_safe_and_epsilon_optimal_on_its_actual_reachable_benchmark
    (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (threshold : ℝ) (seed : Set X) (hseed_nonempty : seed.Nonempty)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) (rawLower rawUpper : ℕ → X → ℝ)
    (hraw : ∀ j x, f x ∈ Icc (rawLower (j + 1) x) (rawUpper (j + 1) x))
    (query : ℕ → X)
    (hquery : ∀ j, query j = actualInitializedQuery f constant hf threshold seed hseed_nonempty
      hseed rawLower rawUpper hraw j)
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda : ℝ) (hlambda : 0 < lambda)
    (mean : ℕ → X → ℝ) (beta : ℕ → ℝ) (horizon : ℕ)
    (hpositive : 0 < horizon / ((actualReachableClosure f constant threshold 0 seed).ncard + 1))
    (multiplier epsilon : ℝ) (hmultiplier : 0 ≤ multiplier) (hepsilon : 0 ≤ epsilon)
    (hbeta : ∀ j < horizon, beta j ≤ multiplier)
    (hshape : ∀ j < horizon, Icc (rawLower (j + 1) (query j)) (rawUpper (j + 1) (query j)) =
      Icc (mean j (query j) - beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j))
        (mean j (query j) + beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j)))
    (hbudget : 8 * multiplier ^ 2 * actualFiniteMaximumKernelInformationGain kernel lambda horizon /
      Real.log (1 + 1 / lambda) ≤
        ((horizon / ((actualReachableClosure f constant threshold 0 seed).ncard + 1) : ℕ) : ℝ) * epsilon ^ 2) :
    (∀ j, threshold ≤ f (query j)) ∧
    ∃ optimum : ℝ,
      IsGreatest (f '' actualReachableClosure f constant threshold epsilon seed) optimum ∧
      ∀ j, horizon ≤ j → optimum - f (actualInitializedReport f constant hf threshold seed hseed_nonempty
        hseed rawLower rawUpper hraw j) ≤ epsilon := by
  classical
  have hrun := actual_initialized_source_run_is_nonempty_nested_zero_reachable_and_safe
    f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw
  have hbands := actual_initialized_confidence_truth_derives_valid_monotone_bands_and_the_seed_floor
    f seed threshold rawLower rawUpper hraw hseed
  have hcard := (actual_zero_reachable_finset_has_exact_membership_and_cardinality
    f constant threshold seed).2
  refine ⟨?_,?_⟩
  · intro j
    rw [hquery j]
    exact actual_initialized_width_maximizing_source_query_is_safe
      f constant hf threshold seed hseed_nonempty hseed rawLower rawUpper hraw j
  · have hquery_actual : ∀ j, query j = actualFiniteQuery
        (actualInitializedSafeFinset seed threshold rawLower constant j)
        (actualContainedLower seed threshold rawLower j) (actualContainedUpper rawUpper j)
        (fun x y => constant * dist x y) threshold (hrun.1 j)
        (fun x _ => (hbands.1 j x).1.trans (hbands.1 j x).2) := by
      intro j
      exact hquery j
    have hraw_contained : ∀ j < horizon,
        Icc (actualContainedLower seed threshold rawLower j (query j))
          (actualContainedUpper rawUpper j (query j)) ⊆
        Icc (mean j (query j) - beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j))
          (mean j (query j) + beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) := by
      intro j hj
      rw [← hshape j hj]
      exact actual_initialized_interval_is_contained_in_its_current_source_raw_band
        seed threshold rawLower rawUpper j (query j)
    have hpositive_actual : 0 < horizon / ((actualZeroReachableFinset f constant threshold seed).card + 1) := by
      simpa only [hcard] using hpositive
    have hbudget_actual : 8 * multiplier ^ 2 * actualFiniteMaximumKernelInformationGain kernel lambda horizon /
        Real.log (1 + 1 / lambda) ≤
        ((horizon / ((actualZeroReachableFinset f constant threshold seed).card + 1) : ℕ) : ℝ) * epsilon ^ 2 := by
      simpa only [hcard] using hbudget
    exact actual_normalized_finite_kernel_information_budget_certifies_the_actual_safeopt_run
      (actualInitializedSafeFinset seed threshold rawLower constant)
      (actualZeroReachableFinset f constant threshold seed) seed f
      (actualContainedLower seed threshold rawLower) (actualContainedUpper rawUpper) mean constant threshold
      hrun.1 hrun.2.1 hrun.2.2.1 hseed_nonempty hrun.2.2.2.1
      (fun j x _ => hbands.1 j x) hbands.2.1 hbands.2.2.1
      (actual_initialized_finite_run_has_the_literal_source_safe_update seed threshold rawLower constant)
      query hquery_actual kernel hkernel hnormalized lambda hlambda beta horizon hpositive_actual
      multiplier epsilon hmultiplier hepsilon hbeta hraw_contained hbudget_actual

end SafeLearning.CompleteModulesSafeOptReachableKernelRun
