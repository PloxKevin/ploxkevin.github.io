import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteModulesLandscapeClosedScalarFeasibility

/-- A closed real objective image cannot have supremum zero without a feasible
point. A positive extended supremum does not need attainment. -/
theorem actual_closed_objective_image_and_nonnegative_extended_supremum_supply_a_feasible_input
    {E : Type*} (U : Set E) (f : E → ℝ) (hclosed : IsClosed (f '' U))
    (hsup : (0 : EReal) ≤ sSup ((fun u => (f u : EReal)) '' U)) :
    ∃ u ∈ U, 0 ≤ f u := by
  by_cases hpositive : (0 : EReal) < sSup ((fun u => (f u : EReal)) '' U)
  · obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := lt_sSup_iff.mp hpositive
    refine ⟨u, hu, ?_⟩
    change (0 : EReal) < (f u : EReal) at hy
    exact (EReal.coe_lt_coe_iff.mp hy).le
  · have heq : sSup ((fun u => (f u : EReal)) '' U) = 0 :=
      le_antisymm (le_of_not_gt hpositive) hsup
    have hnonempty : U.Nonempty := by
      by_contra hn
      have he : U = ∅ := not_nonempty_iff_eq_empty.mp hn
      simp [he] at hsup
    have hbound : BddAbove (f '' U) := by
      refine ⟨0, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      have hle : (f u : EReal) ≤ 0 :=
        heq ▸ le_sSup (mem_image_of_mem (fun u => (f u : EReal)) hu)
      exact EReal.coe_le_coe_iff.mp hle
    have hattained : sSup (f '' U) ∈ f '' U :=
      hclosed.csSup_mem (hnonempty.image f) hbound
    obtain ⟨u, hu, hval⟩ := hattained
    have heupper : sSup ((fun u => (f u : EReal)) '' U) ≤
        ((sSup (f '' U) : ℝ) : EReal) := by
      apply sSup_le
      rintro y ⟨v, hv, rfl⟩
      exact EReal.coe_le_coe (le_csSup hbound (mem_image_of_mem f hv))
    refine ⟨u, hu, ?_⟩
    have hnonneg := hsup.trans heupper
    rw [← hval] at hnonneg
    exact EReal.coe_le_coe_iff.mp hnonneg

/-- An affine scalar objective maps any closed scalar input set to a closed
set, including its constant-coefficient case. -/
theorem actual_scalar_affine_objective_has_closed_image_on_every_closed_input_set
    (U : Set ℝ) (hU : IsClosed U) (a b : ℝ) :
    IsClosed ((fun u => a + b * u) '' U) := by
  by_cases hb : b = 0
  · subst b
    by_cases hne : U.Nonempty
    · have he : (fun u : ℝ => a + 0 * u) '' U = {a} := by
        ext y
        constructor
        · rintro ⟨u, _, rfl⟩
          simp
        · intro hy
          obtain ⟨u, hu⟩ := hne
          refine ⟨u, hu, ?_⟩
          simpa using hy.symm
      rw [he]
      exact isClosed_singleton
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hne
      simp [he]
  · let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ b hb).trans (Homeomorph.addLeft a)
    have he : (fun u : ℝ => a + b * u) = e := by
      funext u
      rfl
    rw [he]
    exact e.isClosedMap U hU

/-- The actual extended supremum condition is sufficient for affine scalar
feasibility on every closed scalar domain, even if it is unbounded. -/
theorem actual_closed_scalar_affine_input_domain_supremum_condition_is_sufficient
    (U : Set ℝ) (hU : IsClosed U) (a b : ℝ)
    (hsup : (0 : EReal) ≤ sSup ((fun u => ((a + b * u : ℝ) : EReal)) '' U)) :
    ∃ u ∈ U, 0 ≤ a + b * u := by
  exact actual_closed_objective_image_and_nonnegative_extended_supremum_supply_a_feasible_input
    U (fun u => a + b * u)
    (actual_scalar_affine_objective_has_closed_image_on_every_closed_input_set U hU a b) hsup

/-- In particular the literal zero-supremum case on a closed interval has an
allowed feasible input. Its attainment is derived, not assumed. -/
theorem actual_closed_scalar_interval_zero_supremum_is_attained_at_a_feasible_input
    (l r a b : ℝ)
    (hsup : sSup ((fun u => ((a + b * u : ℝ) : EReal)) '' Icc l r) = 0) :
    ∃ u ∈ Icc l r, a + b * u = 0 := by
  obtain ⟨u, hu, hnonneg⟩ :=
    actual_closed_scalar_affine_input_domain_supremum_condition_is_sufficient
      (Icc l r) isClosed_Icc a b (by rw [hsup])
  refine ⟨u, hu, le_antisymm ?_ hnonneg⟩
  have hle : ((a + b * u : ℝ) : EReal) ≤ 0 :=
    hsup ▸ le_sSup (mem_image_of_mem (fun u => ((a + b * u : ℝ) : EReal)) hu)
  exact EReal.coe_le_coe_iff.mp hle

end SafeLearning.CompleteModulesLandscapeClosedScalarFeasibility
