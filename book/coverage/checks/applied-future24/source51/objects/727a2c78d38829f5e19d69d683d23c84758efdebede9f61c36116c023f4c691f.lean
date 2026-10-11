import SafeLearning.CompleteModulesSafeOptGPInformationBudget
import SafeLearning.CompleteModulesSafeOptFiniteRunOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteModulesSafeOptKernelRunOptimality

open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptFiniteStageWidth
open SafeLearning.CompleteModulesSafeOptFiniteRunOptimality
open SafeLearning.CompleteModulesSafeOptGPInformationBudget
open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure

variable {X : Type*} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] [Nonempty X]

/-- Actual normalized finite-kernel posterior standard deviations and maximum
information gain instantiate the finite SafeOpt proof. Raw-band containment
derives the query-radius bound; valid confidence is still a separate primitive
event, with no probabilistic GP confidence or RKHS theorem promoted here. -/
theorem actual_normalized_finite_kernel_information_budget_certifies_the_actual_safeopt_run
    (safe : ℕ → Finset X) (bound : Finset X) (seed : Set X)
    (f : X → ℝ) (lower upper mean : ℕ → X → ℝ) (constant : NNReal) (threshold : ℝ)
    (hs : ∀ j, (safe j).Nonempty)
    (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j) (hbound : ∀ j, safe j ⊆ bound)
    (hseed_nonempty : seed.Nonempty) (hseed : seed ⊆ (safe 0 : Set X))
    (hconfidence : ∀ j x, x ∈ bound → lower j x ≤ f x ∧ f x ≤ upper j x)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x)
    (hupper : ∀ i j, i ≤ j → ∀ x, upper j x ≤ upper i x)
    (hupdate : ∀ j, (safe (j + 1) : Set X) =
      actualExpansion (safe j : Set X) (lower (j + 1)) constant threshold)
    (query : ℕ → X)
    (hquery : ∀ j, query j = actualFiniteQuery (safe j) (lower j) (upper j)
      (fun x y => constant * dist x y) threshold (hs j)
      (fun x hx => (hconfidence j x (hbound j hx)).1.trans (hconfidence j x (hbound j hx)).2))
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda : ℝ) (hlambda : 0 < lambda)
    (beta : ℕ → ℝ) (horizon : ℕ) (hpositive : 0 < horizon / (bound.card + 1))
    (multiplier epsilon : ℝ) (hmultiplier : 0 ≤ multiplier) (hepsilon : 0 ≤ epsilon)
    (hbeta : ∀ j < horizon, beta j ≤ multiplier)
    (hraw : ∀ j < horizon, Icc (lower j (query j)) (upper j (query j)) ⊆
      Icc (mean j (query j) - beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j))
        (mean j (query j) + beta j * Real.sqrt (actualKernelSequentialVariance kernel lambda query j)))
    (hbudget : 8 * multiplier ^ 2 * actualFiniteMaximumKernelInformationGain kernel lambda horizon /
      Real.log (1 + 1 / lambda) ≤ ((horizon / (bound.card + 1) : ℕ) : ℝ) * epsilon ^ 2) :
    ∃ optimum : ℝ,
      IsGreatest (f '' actualReachableClosure f constant threshold epsilon seed) optimum ∧
      ∀ j, horizon ≤ j → optimum - f (actualFiniteReport (safe j) (lower j) (hs j)) ≤ epsilon := by
  classical
  have hprimitives :=
    actual_normalized_finite_kernel_standard_deviations_satisfy_the_actual_maximum_information_budget
      kernel hkernel hnormalized lambda hlambda query horizon
  have hradius : ∀ j < horizon, actualWidth (lower j) (upper j)
      (actualFiniteQuery (safe j) (lower j) (upper j) (fun x y => constant * dist x y) threshold
        (hs j) (fun x hx => (hconfidence j x (hbound j hx)).1.trans
          (hconfidence j x (hbound j hx)).2)) ≤
      2 * multiplier * Real.sqrt (actualKernelSequentialVariance kernel lambda query j) := by
    intro j hj
    have hsafe : query j ∈ safe j := by
      rw [hquery j]
      exact (Finset.mem_filter.mp
        (actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
          (safe j) (lower j) (upper j) (fun x y => constant * dist x y) threshold (hs j)
          (fun x hx => (hconfidence j x (hbound j hx)).1.trans
            (hconfidence j x (hbound j hx)).2)).1).1
    have hband := (hconfidence j (query j) (hbound j hsafe)).1.trans
      (hconfidence j (query j) (hbound j hsafe)).2
    have hwidth := actual_contained_confidence_band_has_width_at_most_twice_the_raw_radius
      (lower j (query j)) (upper j (query j)) (mean j (query j)) (beta j)
      (Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) hband (hraw j hj)
    have hmultiplied := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbeta j hj) (by norm_num : (0 : ℝ) ≤ 2))
      (Real.sqrt_nonneg (actualKernelSequentialVariance kernel lambda query j))
    have h := hwidth.trans hmultiplied
    simpa only [actualWidth,hquery j] using h
  exact actual_finite_safeopt_run_information_budget_forces_all_later_reachable_report_optimality
    safe bound seed f lower upper constant threshold hs hmono hbound hseed_nonempty hseed
    hconfidence hlower hupper hupdate
    (fun j => Real.sqrt (actualKernelSequentialVariance kernel lambda query j)) horizon hpositive
    multiplier lambda (actualFiniteMaximumKernelInformationGain kernel lambda horizon) epsilon
    hmultiplier hlambda hepsilon hradius (fun j _ => hprimitives.1 j) hprimitives.2 hbudget

end SafeLearning.CompleteModulesSafeOptKernelRunOptimality
