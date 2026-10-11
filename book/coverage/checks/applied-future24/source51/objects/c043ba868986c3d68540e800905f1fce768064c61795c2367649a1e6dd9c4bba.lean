import SafeLearning.CompleteModulesSafeOptFiniteOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteModulesSafeOptPersistentReport

open SafeLearning.CompleteModulesSafeOptFiniteOptimality
open SafeLearning.CompleteModulesSafeOptConfidenceIntersections

variable {X : Type*}

/-- The true finite maximizer belongs to the actual potential-maximizer set.
A narrow acquisition query therefore bounds every true value by the report's
lower band, which is stronger than a bound by its current true value. -/
theorem actual_small_query_width_bounds_all_safe_values_by_the_report_lower_band
    (safe : Finset X) (f lower upper : X → ℝ) (cost : X → X → ℝ)
    (threshold : ℝ) (hs : safe.Nonempty)
    (hconfidence : ∀ x ∈ safe, lower x ≤ f x ∧ f x ≤ upper x)
    (epsilon : ℝ)
    (hwidth : actualWidth lower upper (actualFiniteQuery safe lower upper cost threshold hs
      (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)) ≤ epsilon) :
    ∀ x ∈ safe, f x ≤ lower (actualFiniteReport safe lower hs) + epsilon := by
  classical
  obtain ⟨hm,hmaximum⟩ :=
    actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band safe f hs
  have hpotential : actualFiniteReport safe f hs ∈ actualMaximizers (safe : Set X) lower upper := by
    refine ⟨hm,?_⟩
    intro y hy
    exact (hconfidence y hy).1.trans ((hmaximum y hy).trans (hconfidence _ hm).2)
  have hcandidate : actualFiniteReport safe f hs ∈
      actualFiniteCandidates safe lower upper cost threshold := by
    simp only [actualFiniteCandidates,Finset.mem_filter]
    exact ⟨hm,Or.inr hpotential⟩
  have hnarrow := ((actual_finite_query_is_a_width_maximizer_over_the_literal_candidate_union
    safe lower upper cost threshold hs
    (fun x hx => (hconfidence x hx).1.trans (hconfidence x hx).2)).2 _ hcandidate).trans hwidth
  have hreport := (actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band
    safe lower hs).2 _ hm
  intro x hx
  have htrue := hmaximum x hx
  have hupper := (hconfidence _ hm).2
  dsimp only [actualWidth] at hnarrow
  linarith

/-- Growing safe sets and increasing lower bands preserve the same actual
epsilon guarantee for the actual later lower-band report. -/
theorem actual_lower_report_certificate_persists_at_every_later_nested_safe_set
    (oldSafe newSafe : Finset X) (comparison : Set X) (f oldLower newLower newUpper : X → ℝ)
    (hold : oldSafe.Nonempty) (hnew : newSafe.Nonempty)
    (hnested : oldSafe ⊆ newSafe) (hcomparison : comparison ⊆ (oldSafe : Set X))
    (hlower : ∀ x ∈ oldSafe, oldLower x ≤ newLower x)
    (hconfidence : ∀ x ∈ newSafe, newLower x ≤ f x ∧ f x ≤ newUpper x)
    (epsilon : ℝ)
    (hcertificate : ∀ x ∈ oldSafe, f x ≤ oldLower (actualFiniteReport oldSafe oldLower hold) + epsilon) :
    ∀ x ∈ comparison, f x ≤ f (actualFiniteReport newSafe newLower hnew) + epsilon := by
  obtain ⟨hreport,_⟩ := actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band
    oldSafe oldLower hold
  have hreport_new := hnested hreport
  have hgrowth := hlower _ hreport
  have hmaximum := (actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band
    newSafe newLower hnew).2 _ hreport_new
  have hvalid := (hconfidence _ (actual_finite_report_is_in_the_safe_set_and_maximizes_the_lower_band
    newSafe newLower hnew).1).1
  intro x hx
  have h := hcertificate x (hcomparison hx)
  linarith

/-- A finite nonempty comparison set has an actual attained true benchmark.
The lower-band certificate gives epsilon optimality at every later round. -/
theorem actual_persistent_lower_report_certificate_has_an_attained_all_later_benchmark
    (safe : ℕ → Finset X) (comparison : Set X) (f : X → ℝ) (lower upper : ℕ → X → ℝ)
    (hs : ∀ j, (safe j).Nonempty)
    (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j)
    (hlower : ∀ i j, i ≤ j → ∀ x, lower i x ≤ lower j x)
    (hconfidence : ∀ j x, x ∈ safe j → lower j x ≤ f x ∧ f x ≤ upper j x)
    (stage : ℕ) (hcomparison : comparison ⊆ (safe stage : Set X))
    (hnonempty : comparison.Nonempty) (epsilon : ℝ)
    (hcertificate : ∀ x ∈ safe stage,
      f x ≤ lower stage (actualFiniteReport (safe stage) (lower stage) (hs stage)) + epsilon) :
    ∃ optimum : ℝ, IsGreatest (f '' comparison) optimum ∧
      ∀ j, stage ≤ j → optimum - f (actualFiniteReport (safe j) (lower j) (hs j)) ≤ epsilon := by
  have hfinite := (safe stage).finite_toSet.subset hcomparison
  obtain ⟨optimum,hgreatest⟩ := (hfinite.image f).isCompact.exists_isGreatest (hnonempty.image f)
  refine ⟨optimum,hgreatest,?_⟩
  intro j hj
  have hpersistent := actual_lower_report_certificate_persists_at_every_later_nested_safe_set
    (safe stage) (safe j) comparison f (lower stage) (lower j) (upper j)
    (hs stage) (hs j) (hmono stage j hj) hcomparison
    (fun x _ => hlower stage j hj x) (hconfidence j) epsilon hcertificate
  obtain ⟨x,hx,hvalue⟩ := hgreatest.1
  have h := hpersistent x hx
  rw [hvalue] at h
  linarith

end SafeLearning.CompleteModulesSafeOptPersistentReport
