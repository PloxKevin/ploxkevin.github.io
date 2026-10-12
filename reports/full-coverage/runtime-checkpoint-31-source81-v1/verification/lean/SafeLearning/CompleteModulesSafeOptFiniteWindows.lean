import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteModulesSafeOptFiniteWindows

variable {X : Type*}

/-- In a monotone finite safe run, one of cardinality-plus-one disjoint
windows has unchanged endpoints. The finite bound is an actual set bound. -/
theorem actual_finite_safe_run_has_an_unchanged_expansion_window
    (safe : ℕ → Finset X) (bound : Finset X)
    (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j)
    (hbound : ∀ j, safe j ⊆ bound) (N : ℕ) :
    ∃ k < bound.card + 1, safe (k * N) = safe ((k + 1) * N) := by
  by_contra hnone
  push Not at hnone
  have hcount : ∀ k, k ≤ bound.card + 1 → k ≤ (safe (k * N)).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk' : k < bound.card + 1 := by omega
      have hsubset := hmono (k * N) ((k + 1) * N)
        (Nat.mul_le_mul_right N (Nat.le_succ k))
      have hstrict := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset,hnone k hk'⟩)
      have hprevious := ih (by omega)
      omega
  have hlower := hcount (bound.card + 1) le_rfl
  have hupper := Finset.card_le_card (hbound ((bound.card + 1) * N))
  omega

/-- Equal safe endpoints force every intervening safe set to equal them. -/
theorem actual_monotone_safe_run_is_constant_between_equal_endpoints
    (safe : ℕ → Finset X) (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j)
    (start N : ℕ) (hequal : safe start = safe (start + N)) :
    ∀ j ≤ N, safe (start + j) = safe start := by
  intro j hj
  apply Finset.Subset.antisymm
  · have hsubset := hmono (start + j) (start + N) (Nat.add_le_add_left hj start)
    rw [← hequal] at hsubset
    exact hsubset
  · exact hmono start (start + j) (Nat.le_add_right start j)

/-- The source's integer allocation uses precisely the floor quotient.
A positive quotient gives an unchanged whole window ending by the horizon. -/
theorem actual_integer_floor_allocation_yields_a_positive_constant_safe_window
    (safe : ℕ → Finset X) (bound : Finset X)
    (hmono : ∀ i j, i ≤ j → safe i ⊆ safe j)
    (hbound : ∀ j, safe j ⊆ bound) (horizon : ℕ)
    (hpositive : 0 < horizon / (bound.card + 1)) :
    ∃ k < bound.card + 1,
      (k + 1) * (horizon / (bound.card + 1)) ≤ horizon ∧
      ∀ j ≤ horizon / (bound.card + 1),
        safe (k * (horizon / (bound.card + 1)) + j) =
          safe (k * (horizon / (bound.card + 1))) := by
  obtain ⟨k,hk,hequal⟩ := actual_finite_safe_run_has_an_unchanged_expansion_window
    safe bound hmono hbound (horizon / (bound.card + 1))
  have hfinish : (k + 1) * (horizon / (bound.card + 1)) ≤ horizon :=
    (Nat.mul_le_mul_right (horizon / (bound.card + 1)) (by omega)).trans
      (Nat.mul_div_le horizon (bound.card + 1))
  have hequal' : safe (k * (horizon / (bound.card + 1))) =
      safe (k * (horizon / (bound.card + 1)) + horizon / (bound.card + 1)) := by
    simpa only [Nat.add_mul,one_mul] using hequal
  refine ⟨k,hk,hfinish,?_⟩
  exact actual_monotone_safe_run_is_constant_between_equal_endpoints
    safe hmono _ _ hequal'

/-- A nonnegative all-round budget bounds the actual sum in any whole
window lying before the horizon, without assuming its desired conclusion. -/
theorem actual_nonnegative_horizon_budget_bounds_every_contained_window
    (value : ℕ → ℝ) (start N horizon : ℕ)
    (hfinish : start + N ≤ horizon)
    (hnonnegative : ∀ j < horizon, 0 ≤ value j) :
    (∑ j ∈ Finset.range N, value (start + j)) ≤
      ∑ j ∈ Finset.range horizon, value j := by
  have hprefix : 0 ≤ ∑ j ∈ Finset.range start, value j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hnonnegative j ((Finset.mem_range.mp hj).trans_le (by omega))
  have hsplit := Finset.sum_range_add value start N
  have hwindow : (∑ j ∈ Finset.range N, value (start + j)) ≤
      ∑ j ∈ Finset.range (start + N), value j := by
    rw [hsplit]
    linarith
  apply hwindow.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hfinish)
  intro j hj _
  exact hnonnegative j (Finset.mem_range.mp hj)

end SafeLearning.CompleteModulesSafeOptFiniteWindows
