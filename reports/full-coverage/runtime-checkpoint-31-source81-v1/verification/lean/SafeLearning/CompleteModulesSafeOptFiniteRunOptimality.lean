import SafeLearning.CompleteModulesSafeOptFiniteStageWidth
import SafeLearning.CompleteModulesSafeOptFiniteWindows
import SafeLearning.CompleteModulesSafeOptPersistentReport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteModulesSafeOptFiniteRunOptimality

open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptFiniteStageWidth
open SafeLearning.CompleteModulesSafeOptFiniteWindows
open SafeLearning.CompleteModulesSafeOptPersistentReport
open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure

variable {X : Type*} [PseudoMetricSpace X]

/-- A genuine finite expanding SafeOpt run becomes epsilon optimal, and its
actual later reports preserve this guarantee. The hypothesis is the literal
integer-window information budget, with floor division retained. Confidence,
raw posterior-radius, and sequential information inequalities are explicit
primitive hypotheses, rather than an assumed stopping or optimality event. -/
theorem actual_finite_safeopt_run_information_budget_forces_all_later_reachable_report_optimality
    (safe : ℕ → Finset X) (bound : Finset X) (seed : Set X)
    (f : X → ℝ) (lower upper : ℕ → X → ℝ) (constant : NNReal) (threshold : ℝ)
    (hs : ∀ j, (safe j).Nonempty)
    (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j) (hbound : ∀ j, safe j ⊆ bound)
    (hseed_nonempty : seed.Nonempty) (hseed : seed ⊆ (safe 0 : Set X))
    (hconfidence : ∀ j x, x ∈ bound → lower j x ≤ f x ∧ f x ≤ upper j x)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x)
    (hupper : ∀ i j, i ≤ j → ∀ x, upper j x ≤ upper i x)
    (hupdate : ∀ j, (safe (j + 1) : Set X) =
      actualExpansion (safe j : Set X) (lower (j + 1)) constant threshold)
    (sigma : ℕ → ℝ) (horizon : ℕ) (hpositive : 0 < horizon / (bound.card + 1))
    (multiplier lambda information epsilon : ℝ) (hmultiplier : 0 ≤ multiplier)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon)
    (hradius : ∀ j < horizon, actualWidth (lower j) (upper j)
      (actualFiniteQuery (safe j) (lower j) (upper j) (fun x y => constant * dist x y) threshold
        (hs j) (fun x hx => (hconfidence j x (hbound j hx)).1.trans
          (hconfidence j x (hbound j hx)).2)) ≤ 2 * multiplier * sigma j)
    (hsigma : ∀ j < horizon, (sigma j) ^ 2 ∈ Icc 0 1)
    (hinformation : ∑ j ∈ Finset.range horizon,
      Real.log (1 + (sigma j) ^ 2 / lambda) ≤ 2 * information)
    (hbudget : 8 * multiplier ^ 2 * information / Real.log (1 + 1 / lambda) ≤
      ((horizon / (bound.card + 1) : ℕ) : ℝ) * epsilon ^ 2) :
    ∃ optimum : ℝ,
      IsGreatest (f '' actualReachableClosure f constant threshold epsilon seed) optimum ∧
      ∀ j, horizon ≤ j → optimum - f (actualFiniteReport (safe j) (lower j) (hs j)) ≤ epsilon := by
  classical
  let N := horizon / (bound.card + 1)
  obtain ⟨k,hk,hfinish,hconstant⟩ :=
    actual_integer_floor_allocation_yields_a_positive_constant_safe_window
      safe bound hmono hbound horizon hpositive
  let start := k * N
  have hN : 0 < N := hpositive
  have hfinish' : start + N ≤ horizon := by
    dsimp only [start,N]
    simpa only [Nat.add_mul,one_mul] using hfinish
  have hconstant' : ∀ j ≤ N, safe (start + j) = safe start := hconstant
  have hconfidence_safe : ∀ j x, x ∈ safe j → lower j x ≤ f x ∧ f x ≤ upper j x :=
    fun j x hx => hconfidence j x (hbound j hx)
  have hradius_window : ∀ j < N, actualWidth (lower (start + j)) (upper (start + j))
      (actualFiniteQuery (safe start) (lower (start + j)) (upper (start + j))
        (fun x y => constant * dist x y) threshold (hs start)
        (fun x hx => (hconfidence (start + j) x (hbound start hx)).1.trans
          (hconfidence (start + j) x (hbound start hx)).2)) ≤ 2 * multiplier * sigma (start + j) := by
    intro j hj
    have h := hradius (start + j) (by omega)
    simpa only [hconstant' j hj.le] using h
  have hlog_nonnegative : ∀ j < horizon, 0 ≤ Real.log (1 + (sigma j) ^ 2 / lambda) := by
    intro j _
    apply Real.log_nonneg
    have h := div_nonneg (sq_nonneg (sigma j)) hlambda.le
    linarith
  have hinformation_window : ∑ j ∈ Finset.range N,
      Real.log (1 + (sigma (start + j)) ^ 2 / lambda) ≤ 2 * information :=
    (actual_nonnegative_horizon_budget_bounds_every_contained_window
      (fun j => Real.log (1 + (sigma j) ^ 2 / lambda)) start N horizon
      hfinish' hlog_nonnegative).trans hinformation
  have hsmall := (actual_finite_stage_information_budget_forces_small_query_width_and_report_optimality
    (safe start) f (fun j => lower (start + j)) (fun j => upper (start + j))
    (fun x y => constant * dist x y) threshold (hs start)
    (fun j x hx => hconfidence (start + j) x (hbound start hx))
    (fun i j hij x => hlower (start + i) (start + j) (Nat.add_le_add_left hij start) x)
    (fun i j hij x => hupper (start + i) (start + j) (Nat.add_le_add_left hij start) x)
    (fun j => sigma (start + j)) N hN multiplier lambda information epsilon
    hmultiplier hlambda hepsilon hradius_window
    (fun j hj => hsigma (start + j) (by omega)) hinformation_window hbudget).1
  have hwidth : actualWidth (lower (start + N)) (upper (start + N))
      (actualFiniteQuery (safe (start + N)) (lower (start + N)) (upper (start + N))
        (fun x y => constant * dist x y) threshold (hs (start + N))
        (fun x hx => (hconfidence_safe (start + N) x hx).1.trans
          (hconfidence_safe (start + N) x hx).2)) ≤ epsilon := by
    simpa only [hconstant' N le_rfl] using hsmall
  have hupdate_final : actualExpansion (safe (start + N) : Set X) (lower (start + N))
      constant threshold ⊆ (safe (start + N) : Set X) := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    have hprior := hconstant' n (by omega)
    have h := hupdate (start + n)
    have hindex : start + n + 1 = start + N := by omega
    rw [hindex,hprior,hconstant' N le_rfl] at h
    rw [hconstant' N le_rfl,← h]
  have hseed_final : seed ⊆ (safe (start + N) : Set X) :=
    hseed.trans (hmono 0 (start + N) (Nat.zero_le _))
  have hcontains := (actual_finite_safeopt_stopping_certificate_proves_reachable_report_optimality
    (safe (start + N)) seed f (lower (start + N)) (upper (start + N)) constant threshold
    (hs (start + N)) hseed_final (hconfidence_safe (start + N)) epsilon hepsilon hwidth hupdate_final).1
  have hcertificate := actual_small_query_width_bounds_all_safe_values_by_the_report_lower_band
    (safe (start + N)) f (lower (start + N)) (upper (start + N))
    (fun x y => constant * dist x y) threshold (hs (start + N))
    (hconfidence_safe (start + N)) epsilon hwidth
  have hreachable_nonempty : (actualReachableClosure f constant threshold epsilon seed).Nonempty := by
    obtain ⟨x,hx⟩ := hseed_nonempty
    exact ⟨x,mem_iUnion.mpr ⟨0,hx⟩⟩
  obtain ⟨optimum,hgreatest,hpersistent⟩ :=
    actual_persistent_lower_report_certificate_has_an_attained_all_later_benchmark
      safe (actualReachableClosure f constant threshold epsilon seed) f lower upper hs hmono hlower
      hconfidence_safe (start + N) hcontains hreachable_nonempty epsilon hcertificate
  exact ⟨optimum,hgreatest,fun j hj => hpersistent j (hfinish'.trans hj)⟩

end SafeLearning.CompleteModulesSafeOptFiniteRunOptimality
