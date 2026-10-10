import SafeLearning.CompleteModulesSafeOptFiniteOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace SafeLearning.CompleteModulesSafeOptFiniteStageWidth

open SafeLearning.CompleteModulesSafeOptConfidenceIntersections
open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptPracticeTheorems
open SafeLearning.CompleteModulesSafeOptReachableClosure

/-- Containment in the actual raw mean-plus/minus band bounds interval width. -/
theorem actual_contained_confidence_band_has_width_at_most_twice_the_raw_radius
    (lower upper mean multiplier sigma : ℝ) (hband : lower ≤ upper)
    (hcontained : Icc lower upper ⊆ Icc (mean - multiplier * sigma) (mean + multiplier * sigma)) :
    upper - lower ≤ 2 * multiplier * sigma := by
  have hl := (hcontained (show lower ∈ Icc lower upper from ⟨le_rfl,hband⟩)).1
  have hu := (hcontained (show upper ∈ Icc lower upper from ⟨hband,le_rfl⟩)).2
  linarith

/-- Concavity of the logarithm proves the normalized-variance information
inequality used in SafeOpt's width-sum constant. -/
theorem actual_unit_bounded_variance_is_controlled_by_its_sequential_log_factor
    (lambda variance : ℝ) (hlambda : 0 < lambda) (hvariance : variance ∈ Icc 0 1) :
    variance * Real.log (1 + 1 / lambda) ≤ Real.log (1 + variance / lambda) := by
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 1 + 1 / lambda ∈ Ioi 0 by
      change (0 : ℝ) < 1 + 1 / lambda
      positivity)
    (show 0 ≤ 1 - variance by linarith [hvariance.2]) hvariance.1
    (show (1 - variance) + variance = 1 by ring)
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at hlog
  convert hlog using 1
  congr 1
  ring

/-- Actual nonnegative widths bounded by posterior-style radii obey the
literal 8/log(1+1/lambda) information budget. No decay conclusion is assumed. -/
theorem actual_sequential_variance_information_budget_bounds_the_sum_of_squared_query_widths
    (width sigma : ℕ → ℝ) (N : ℕ) (multiplier lambda information : ℝ)
    (hmultiplier : 0 ≤ multiplier) (hlambda : 0 < lambda)
    (hwidth : ∀ j < N, 0 ≤ width j ∧ width j ≤ 2 * multiplier * sigma j)
    (hsigma : ∀ j < N, (sigma j) ^ 2 ∈ Icc 0 1)
    (hinformation : ∑ j ∈ Finset.range N, Real.log (1 + (sigma j) ^ 2 / lambda) ≤ 2 * information) :
    ∑ j ∈ Finset.range N, (width j) ^ 2 ≤
      8 * multiplier ^ 2 * information / Real.log (1 + 1 / lambda) := by
  have hlogpos : 0 < Real.log (1 + 1 / lambda) :=
    Real.log_pos (by
      have hi : 0 < 1 / lambda := by positivity
      linarith)
  have hvariance : ∑ j ∈ Finset.range N, (sigma j) ^ 2 ≤
      2 * information / Real.log (1 + 1 / lambda) := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      (∑ j ∈ Finset.range N, (sigma j) ^ 2) * Real.log (1 + 1 / lambda) =
          ∑ j ∈ Finset.range N, (sigma j) ^ 2 * Real.log (1 + 1 / lambda) := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ Finset.range N, Real.log (1 + (sigma j) ^ 2 / lambda) := by
        apply Finset.sum_le_sum
        intro j hj
        exact actual_unit_bounded_variance_is_controlled_by_its_sequential_log_factor
          lambda ((sigma j) ^ 2) hlambda (hsigma j (Finset.mem_range.mp hj))
      _ ≤ 2 * information := hinformation
  calc
    (∑ j ∈ Finset.range N, (width j) ^ 2) ≤
        ∑ j ∈ Finset.range N, 4 * multiplier ^ 2 * (sigma j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hw := hwidth j (Finset.mem_range.mp hj)
      calc
        (width j) ^ 2 ≤ (2 * multiplier * sigma j) ^ 2 := pow_le_pow_left₀ hw.1 hw.2 2
        _ = 4 * multiplier ^ 2 * (sigma j) ^ 2 := by ring
    _ = 4 * multiplier ^ 2 * ∑ j ∈ Finset.range N, (sigma j) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * multiplier ^ 2 * (2 * information / Real.log (1 + 1 / lambda)) :=
      mul_le_mul_of_nonneg_left hvariance (mul_nonneg (by norm_num) (pow_nonneg hmultiplier 2))
    _ = 8 * multiplier ^ 2 * information / Real.log (1 + 1 / lambda) := by ring

variable {X : Type*}

/-- Tightening actual bands on a fixed certified finite set decreases the
width selected by the actual finite acquisition rule. -/
theorem actual_finite_stage_query_width_decreases_when_the_bands_tighten
    (safe : Finset X) (oldLower oldUpper newLower newUpper : X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) (hs : safe.Nonempty)
    (hold : ∀ x ∈ safe, oldLower x ≤ oldUpper x)
    (hnew : ∀ x ∈ safe, newLower x ≤ newUpper x)
    (hl : ∀ x, oldLower x ≤ newLower x) (hu : ∀ x, newUpper x ≤ oldUpper x) :
    actualWidth newLower newUpper (actualFiniteQuery safe newLower newUpper cost threshold hs hnew) ≤
      actualWidth oldLower oldUpper (actualFiniteQuery safe oldLower oldUpper cost threshold hs hold) := by
  classical
  obtain ⟨hqnew,_⟩ := actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    safe newLower newUpper cost threshold hs hnew
  obtain ⟨_,hqold⟩ := actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    safe oldLower oldUpper cost threshold hs hold
  have hc := (Finset.mem_filter.mp hqnew).2
  have hsub := (actual_constant_safe_stage_candidates_shrink_when_intersected_endpoints_tighten
    (safe : Set X) oldLower oldUpper newLower newUpper cost threshold hl hu).2.2
  have hcold := hsub hc
  have hmemold : actualFiniteQuery safe newLower newUpper cost threshold hs hnew ∈
      actualFiniteCandidates safe oldLower oldUpper cost threshold := by
    simp only [actualFiniteCandidates,Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hqnew).1,hcold⟩
  have hwidth := hqold _ hmemold
  have hlow := hl (actualFiniteQuery safe newLower newUpper cost threshold hs hnew)
  have hupp := hu (actualFiniteQuery safe newLower newUpper cost threshold hs hnew)
  dsimp only [actualWidth] at hwidth ⊢
  linarith

/-- After N observations within a fixed finite certified stage, the actual
next-query width is small whenever the literal sequential information budget
fits N*epsilon^2. The recommendation conclusion is a genuine consequence. -/
theorem actual_finite_stage_information_budget_forces_small_query_width_and_report_optimality
    (safe : Finset X) (f : X → ℝ) (lower upper : ℕ → X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) (hs : safe.Nonempty)
    (hconfidence : ∀ j x, x ∈ safe → lower j x ≤ f x ∧ f x ≤ upper j x)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x)
    (hupper : ∀ i j, i ≤ j → ∀ x, upper j x ≤ upper i x)
    (sigma : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (multiplier lambda information epsilon : ℝ) (hmultiplier : 0 ≤ multiplier)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon)
    (hradius : ∀ j < N, actualWidth (lower j) (upper j)
      (actualFiniteQuery safe (lower j) (upper j) cost threshold hs
        (fun x hx => (hconfidence j x hx).1.trans (hconfidence j x hx).2)) ≤
          2 * multiplier * sigma j)
    (hsigma : ∀ j < N, (sigma j) ^ 2 ∈ Icc 0 1)
    (hinformation : ∑ j ∈ Finset.range N, Real.log (1 + (sigma j) ^ 2 / lambda) ≤ 2 * information)
    (hbudget : 8 * multiplier ^ 2 * information / Real.log (1 + 1 / lambda) ≤ (N : ℝ) * epsilon ^ 2) :
    actualWidth (lower N) (upper N) (actualFiniteQuery safe (lower N) (upper N) cost threshold hs
      (fun x hx => (hconfidence N x hx).1.trans (hconfidence N x hx).2)) ≤ epsilon ∧
    ∀ x ∈ safe, f x ≤ f (actualFiniteReport safe (lower N) hs) + epsilon := by
  classical
  let width : ℕ → ℝ := fun j => actualWidth (lower j) (upper j)
    (actualFiniteQuery safe (lower j) (upper j) cost threshold hs
      (fun x hx => (hconfidence j x hx).1.trans (hconfidence j x hx).2))
  have hnon : ∀ j, 0 ≤ width j := by
    intro j
    have hq := (actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
      safe (lower j) (upper j) cost threshold hs
      (fun x hx => (hconfidence j x hx).1.trans (hconfidence j x hx).2)).1
    have hc := hconfidence j _ (Finset.mem_filter.mp hq).1
    dsimp only [width,actualWidth]
    linarith
  have hstage : ∀ j < N, width N ≤ width j := by
    intro j hj
    exact actual_finite_stage_query_width_decreases_when_the_bands_tighten
      safe (lower j) (upper j) (lower N) (upper N) cost threshold hs
      (fun x hx => (hconfidence j x hx).1.trans (hconfidence j x hx).2)
      (fun x hx => (hconfidence N x hx).1.trans (hconfidence N x hx).2)
      (hlower j N hj.le) (hupper j N hj.le)
  have hsquare := actual_nonincreasing_nonnegative_stage_widths_imply_the_literal_square_sum_bound
    width N (hnon N) hstage
  have hsum := actual_sequential_variance_information_budget_bounds_the_sum_of_squared_query_widths
    width sigma N multiplier lambda information hmultiplier hlambda
    (fun j hj => ⟨hnon j,hradius j hj⟩) hsigma hinformation
  have hsmall : width N ≤ epsilon := by
    by_contra hn
    have hlarge : epsilon < width N := lt_of_not_ge hn
    have hsq : epsilon ^ 2 < (width N) ^ 2 := (sq_lt_sq₀ hepsilon (hnon N)).mpr hlarge
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hmul := mul_lt_mul_of_pos_left hsq hNreal
    exact (not_lt_of_ge (hsquare.trans (hsum.trans hbudget))) hmul
  exact ⟨hsmall,actual_query_width_bound_certifies_the_actual_report_on_the_finite_safe_set
    safe f (lower N) (upper N) cost threshold hs (hconfidence N) epsilon hepsilon hsmall⟩

end SafeLearning.CompleteModulesSafeOptFiniteStageWidth
